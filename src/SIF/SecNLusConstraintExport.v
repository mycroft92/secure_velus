(** Executable export of generated NLustre security constraints.

    This file does not add new proof obligations.  It packages the verified
    computations from [NameInterface] and [SecNLusTyping] into one concrete
    function that can be extracted and called from the OCaml driver.

    Relative to the paper, this is a tooling-only reflection of the NLustre
    source typing phase: it exposes the per-node symbolic constraints and the
    generated source-name to security-name mappings that the later proofs reason
    about abstractly. *)
From Velus Require Import Common.
From Velus Require Import ObcToClight.Interface.
From Velus Require Import Instantiator.
From Velus Require Import Ident.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecNLusTyping.

From Coq Require Import String List.
From compcert Require Import common.Errors.

Import ListNotations.

Module Import Ids := Ident.Ids.
Module Import Op := Interface.Op.
Module CE := Instantiator.CE.
Module NL := Instantiator.NL.
Module Import Syn := NL.Syn.

Module SC := SecMonad Ids.
Module SIG := Signature Ids SC.
Module ConcreteNameGen <: NAMEGEN Ids Op CE.Syn NL.Syn.
Include NAMEGEN Ids Op CE.Syn NL.Syn.
End ConcreteNameGen.
Module ConcreteSecCETyping <: SECCETYPING Ids Op CE.Syn.
Include SECCETYPING Ids Op CE.Syn.
End ConcreteSecCETyping.
Module NAMEGEN := ConcreteNameGen.
Module SECCETYPING := ConcreteSecCETyping.
Module SECNLUSTYPING :=
  SecNLusTyping
    Ids Op SC CE.Syn NL.Syn SIG NAMEGEN SECCETYPING
    CE.IsF CE.Clo NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo.

Record node_constraint_dump := mkNodeConstraintDump {
  dump_name : ident;
  dump_clk : ident;
  dump_rst : ident;
  dump_inputs : list (ident * ident);
  dump_outputs : list (ident * ident);
  dump_locals : list (ident * ident);
  dump_constraints : list SymTypes.constraint
}.

Definition sif_constraint_dump := list node_constraint_dump.

Fixpoint zip_idents (xs ys : list ident) : list (ident * ident) :=
  match xs, ys with
  | x :: xs', y :: ys' => (x, y) :: zip_idents xs' ys'
  | _, _ => []
  end.

Definition build_node_constraint_dump
  (envs : node_scoped_env)
  (aux_names : list node_aux_names)
  (G : SIG.secglobal)
  (n : NL.Syn.node)
  : res node_constraint_dump :=
  match find_node_env n.(n_name) envs with
  | None => Error (MSG "Missing generated local security environment for node "
                    :: CTX n.(n_name) :: nil)
  | Some env =>
      match get_node_aux n.(n_name) aux_names with
      | None => Error (MSG "Missing generated clock/reset names for node "
                        :: CTX n.(n_name) :: nil)
      | Some (clk_id, rst_id) =>
          match get_mappings_from_node n.(n_in) env,
                get_mappings_from_node n.(n_out) env,
                get_mappings_from_node n.(n_vars) env,
                SIG.find_signature n.(n_name) G
          with
          | Some inp_ids, Some out_ids, Some local_ids, Some sig =>
              OK {| dump_name := n.(n_name);
                    dump_clk := sig.(SIG.s_clk);
                    dump_rst := sig.(SIG.s_reset);
                    dump_inputs := zip_idents (map fst n.(n_in)) inp_ids;
                    dump_outputs := zip_idents (map fst n.(n_out)) out_ids;
                    dump_locals := zip_idents (map fst n.(n_vars)) local_ids;
                    dump_constraints := sig.(SIG.s_constraints) |}
          | None, _, _, _ =>
              Error (MSG "Missing generated input mappings for node "
                        :: CTX n.(n_name) :: nil)
          | _, None, _, _ =>
              Error (MSG "Missing generated output mappings for node "
                        :: CTX n.(n_name) :: nil)
          | _, _, None, _ =>
              Error (MSG "Missing generated local mappings for node "
                        :: CTX n.(n_name) :: nil)
          | _, _, _, None =>
              Error (MSG "Missing generated security signature for node "
                        :: CTX n.(n_name) :: nil)
          end
      end
  end.

Fixpoint build_constraint_dump
  (nodes : NL.Syn.global)
  (envs : node_scoped_env)
  (aux_names : list node_aux_names)
  (G : SIG.secglobal)
  : res sif_constraint_dump :=
  match nodes with
  | [] => OK []
  | n :: nodes' =>
      match build_node_constraint_dump envs aux_names G n with
      | Error e => Error e
      | OK d =>
          match build_constraint_dump nodes' envs aux_names G with
          | Error e => Error e
          | OK ds => OK (d :: ds)
          end
      end
  end.

Definition generate_nlustre_constraint_dump
  (nodes : NL.Syn.global)
  : res sif_constraint_dump :=
  (* The extracted NLustre global is stored in reverse construction order,
     while signature generation needs callees before callers.  We therefore
     replay the shared generators on the user-facing node order, matching the
     existing NLustre printer. *)
  let ordered_nodes := rev nodes in
  match NAMEGEN.generate_node_scoped_env ordered_nodes with
  | Error e => Error e
  | OK (envs, aux_names) =>
      match SECNLUSTYPING.generate_all_signatures_scoped_env ordered_nodes envs aux_names with
      | Error e => Error e
      | OK G => build_constraint_dump ordered_nodes envs aux_names G
      end
  end.
