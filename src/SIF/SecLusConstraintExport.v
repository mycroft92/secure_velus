(** Executable export of generated Lustre security signatures and constraints.

    The Lustre counterpart of [SecNLusConstraintExport.v], and the first place
    the Lustre-side stack is applied to the concrete Velus modules rather than
    kept behind module parameters.  That is what makes it a check as well as an
    export: [SECLNAMEGEN], [SECLTYPING] and -- in [Check] below --
    [SECLUSNLUSTRANSLATION] are instantiated at [Instantiator]'s real Lustre,
    CoreExpr, NLustre and Transcription modules.

    [Check] is a functor over the lattice because the repository fixes no
    concrete one: [Lattice] is genuinely a parameter of the security semantics.
    Everything else in it is concrete. *)

From Velus Require Import Common.
From Velus Require Import ObcToClight.Interface.
From Velus Require Import Instantiator.
From Velus Require Import Ident.
From Velus Require Import SIF.SecLattice.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SecMonadStep.
From Velus Require Import SIF.SymTypes.
From Velus Require Import SIF.SecTypes.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecLNameInterface.
From Velus Require Import SIF.SecLTyping.
From Velus Require Import SIF.SecNLusTyping.
From Velus Require Import SIF.SecNLusTypingCorrectness.
From Velus Require Import SIF.SecLusNLusTranslation.
From Velus Require Import SIF.SecLusTypes.
From Velus Require Import SIF.SecLusUnnesting.

From Coq Require Import String List.
From compcert Require Import common.Errors.

Import ListNotations.

Module Import Ids := Ident.Ids.
Module Import Op := Interface.Op.
Module Import OpAux := Interface.OpAux.
Module CE := Instantiator.CE.
Module L := Instantiator.L.
Module NL := Instantiator.NL.
Module TR := Instantiator.TR.

Module SC := SecMonad Ids.
Module SIG := Signature Ids SC.

Module ConcreteNameGen <: NAMEGEN Ids Op CE.Syn NL.Syn.
Include NAMEGEN Ids Op CE.Syn NL.Syn.
End ConcreteNameGen.

Module ConcreteSecCETyping <: SECCETYPING Ids Op CE.Syn CE.IsF CE.Clo.
Include SECCETYPING Ids Op CE.Syn CE.IsF CE.Clo.
End ConcreteSecCETyping.

Module ConcreteSecLNameGen :=
  SecLNameGen Ids Op OpAux L.Syn CE.Syn NL.Syn ConcreteNameGen TR.Tr.

Module ConcreteSecLTyping :=
  SecLTyping Ids Op OpAux SC L.Syn CE.Syn NL.Syn SIG ConcreteNameGen
    CE.IsF CE.Clo ConcreteSecCETyping TR.Tr.

(** * The dump

    Same record as the NLustre export, so the two can be diffed node by node
    on a transcribed program -- which is what [Signature_entails] is about. *)

Record lnode_constraint_dump := mkLNodeConstraintDump {
  ldump_name : ident;
  ldump_clk : ident;
  ldump_rst : ident;
  ldump_inputs : list (ident * ident);
  ldump_outputs : list (ident * ident);
  ldump_locals : list (ident * ident);
  ldump_raw_constraints : list SymTypes.constraint;
  ldump_constraints : list SymTypes.constraint
}.

Definition sif_lconstraint_dump := list lnode_constraint_dump.

Fixpoint zip_idents (xs ys : list ident) : list (ident * ident) :=
  match xs, ys with
  | x :: xs', y :: ys' => (x, y) :: zip_idents xs' ys'
  | _, _ => []
  end.

Definition build_lnode_constraint_dump
  (envs : node_scoped_env)
  (aux_names : list node_aux_names)
  (G : SIG.secglobal)
  (n : L.Syn.node)
  : res lnode_constraint_dump :=
  match find_node_env n.(L.Syn.n_name) envs with
  | None => Error (MSG "Missing generated local security environment for node "
                    :: CTX n.(L.Syn.n_name) :: nil)
  | Some env =>
      match get_node_aux n.(L.Syn.n_name) aux_names with
      | None => Error (MSG "Missing generated clock/reset names for node "
                        :: CTX n.(L.Syn.n_name) :: nil)
      | Some (clk_id, rst_id) =>
          match get_mappings_from_node n.(L.Syn.n_in) env,
                get_mappings_from_node n.(L.Syn.n_out) env,
                get_mappings_from_node n.(L.Syn.n_vars) env,
                SIG.find_signature n.(L.Syn.n_name) G
          with
          | Some inp_ids, Some out_ids, Some local_ids, Some sig =>
              match ConcreteSecLTyping.generate_leqns_constraints
                      G env sig.(SIG.s_clk) sig.(SIG.s_reset)
                      (ConcreteSecLTyping.lnode_clock_env n)
                      n.(L.Syn.n_eqs) SC.init_state with
              | Error e => Error e
              | OK (raw_constraints, _) =>
                  OK {| ldump_name := n.(L.Syn.n_name);
                        ldump_clk := sig.(SIG.s_clk);
                        ldump_rst := sig.(SIG.s_reset);
                        ldump_inputs := zip_idents (map fst n.(L.Syn.n_in)) inp_ids;
                        ldump_outputs := zip_idents (map fst n.(L.Syn.n_out)) out_ids;
                        ldump_locals := zip_idents (map fst n.(L.Syn.n_vars)) local_ids;
                        ldump_raw_constraints := raw_constraints;
                        ldump_constraints := sig.(SIG.s_constraints) |}
              end
          | None, _, _, _ =>
              Error (MSG "Missing generated input mappings for node "
                        :: CTX n.(L.Syn.n_name) :: nil)
          | _, None, _, _ =>
              Error (MSG "Missing generated output mappings for node "
                        :: CTX n.(L.Syn.n_name) :: nil)
          | _, _, None, _ =>
              Error (MSG "Missing generated local mappings for node "
                        :: CTX n.(L.Syn.n_name) :: nil)
          | _, _, _, None =>
              Error (MSG "Missing generated security signature for node "
                        :: CTX n.(L.Syn.n_name) :: nil)
          end
      end
  end.

Fixpoint build_lconstraint_dump
  (nodes : list L.Syn.node)
  (envs : node_scoped_env)
  (aux_names : list node_aux_names)
  (G : SIG.secglobal)
  : res sif_lconstraint_dump :=
  match nodes with
  | [] => OK []
  | n :: nodes' =>
      match build_lnode_constraint_dump envs aux_names G n with
      | Error e => Error e
      | OK d =>
          match build_lconstraint_dump nodes' envs aux_names G with
          | Error e => Error e
          | OK ds => OK (d :: ds)
          end
      end
  end.

(** The accumulator grows front-to-back while [Ordered_nodes] places a callee
    after its caller, so the driver generates over [rev nodes] -- exactly as
    the NLustre one does, which is what lets the two dumps be compared. *)

Definition generate_lustre_constraint_dump
  (nodes : list L.Syn.node)
  : res sif_lconstraint_dump :=
  let ordered_nodes := rev nodes in
  match ConcreteSecLNameGen.generate_lnode_scoped_env ordered_nodes with
  | Error e => Error e
  | OK (envs, aux_names) =>
      match ConcreteSecLTyping.generate_all_lsignatures_scoped_env
              ordered_nodes envs aux_names SC.init_state with
      | Error e => Error e
      | OK G => build_lconstraint_dump ordered_nodes envs aux_names G
      end
  end.

(** * The leg, at the concrete modules

    Nothing here is used by the export; it exists so that the parameter list of
    [SECLUSNLUSTRANSLATION] is checked against the real Velus modules rather
    than only against itself. *)

Module Check (Lat : Lattice).

  Module SecT := SecTypes.SecTypes Lat.
  Module SLT := SecLusTypesFun Lat SecT.
  Module STEP := SecMonadStep Ids SC.

  Module SIGPROOFS <: SIGNATURE_PROOFS Ids SC SIG Lat SecT.
  Include SIGNATURE_PROOFS Ids SC SIG Lat SecT.
  End SIGPROOFS.

  Module SECNLUSTYPING :=
    SecNLusTyping Ids Op SC CE.Syn NL.Syn SIG ConcreteNameGen
      CE.IsF CE.Clo ConcreteSecCETyping NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo.

  Module SECNLC :=
    SecNLusTypingCorrectness Ids Op SC CE.Syn NL.Syn Lat SecT SIG SIGPROOFS
      ConcreteNameGen CE.IsF CE.Clo ConcreteSecCETyping
      NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo SECNLUSTYPING.

  Module Leg :=
    SecLusNLusTranslation Ids Op OpAux SC L.Syn CE.Syn NL.Syn Lat SecT STEP
      SIG SIGPROOFS ConcreteNameGen CE.IsF CE.Clo ConcreteSecCETyping
      NL.Ord NL.Mem NL.IsD NL.IsF NL.Clo TR.Tr ConcreteSecLTyping
      SECNLUSTYPING SECNLC ConcreteSecLNameGen L.Clo L.Ord TR.Clocking.

  (** And the unnesting leg, at the same concrete modules. *)
  Module LegU :=
    SecLusUnnesting Ids Op OpAux Lat SecT SLT SC L.Syn L.Clo CE.Syn NL.Syn STEP SIG
      SIGPROOFS ConcreteNameGen CE.IsF CE.Clo ConcreteSecCETyping TR.Tr
      ConcreteSecLTyping L.Norm.Norm.Unnesting.

End Check.
