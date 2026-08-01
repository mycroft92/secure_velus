(** Executable export of generated Obc security signatures and constraints. *)

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import ObcToClight.Interface.
From Velus Require Import Instantiator.
From Velus Require Import Ident.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecObcTyping.

From Coq Require Import String List.
From compcert Require Import common.Errors.

Import ListNotations.

Module Import Ids := Ident.Ids.
Module Import Op := Interface.Op.
Module Import OpAux := Interface.OpAux.
Module CE := Instantiator.CE.
Module NL := Instantiator.NL.
Module Stc := Instantiator.Stc.
Module Obc := Interface.Obc.
Module Import SynObc := Obc.Syn.

Module SC := SecMonad Ids.
Module SIG := Signature Ids SC.
Module ConcreteNameGen <: NAMEGEN Ids Op CE.Syn NL.Syn.
Include NAMEGEN Ids Op CE.Syn NL.Syn.
End ConcreteNameGen.
Module NAMEGEN := ConcreteNameGen.
Module SECOBCTYPING :=
  SecObcTyping Ids Op OpAux SC Obc.Syn SIG.

Record class_constraint_dump := mkClassConstraintDump {
  obc_dump_name : ident;
  obc_dump_clk : ident;
  obc_dump_rst : ident;
  obc_dump_inputs : list (ident * ident);
  obc_dump_outputs : list (ident * ident);
  obc_dump_locals : list (ident * ident);
  obc_dump_mems : list (ident * ident);
  obc_dump_state_instances : list (ident * ident);
  obc_dump_raw_constraints : list SymTypes.constraint;
  obc_dump_collapsed_constraints : list SymTypes.constraint;
  obc_dump_constraints : list SymTypes.constraint
}.

Definition obc_constraint_dump := list class_constraint_dump.

Fixpoint zip_idents (xs ys : list ident) : list (ident * ident) :=
  match xs, ys with
  | x :: xs', y :: ys' => (x, y) :: zip_idents xs' ys'
  | _, _ => []
  end.

Fixpoint build_state_instance_dump
  (cls_name : ident)
  (objs : list (ident * ident))
  (state_env : Env.t ident)
  : res (list (ident * ident)) :=
  match objs with
  | [] => OK []
  | (o, _) :: objs' =>
      match Env.find o state_env with
      | None =>
          Error (MSG "Missing generated state mapping for class "
                 :: CTX cls_name
                 :: MSG " and instance "
                 :: CTX o
                 :: nil)
      | Some sid =>
          match build_state_instance_dump cls_name objs' state_env with
          | Error e => Error e
          | OK ds => OK ((o, sid) :: ds)
          end
      end
  end.

Definition build_class_constraint_dump
  (envs : node_scoped_env)
  (aux_names : list node_aux_names)
  (G : SIG.secglobal)
  (c : class)
  : res class_constraint_dump :=
  match find_node_env c.(c_name) envs with
  | None =>
      Error (MSG "Missing generated local security environment for class "
             :: CTX c.(c_name) :: nil)
  | Some env =>
      match get_node_aux c.(c_name) aux_names with
      | None =>
          Error (MSG "Missing generated clock/reset names for class "
                 :: CTX c.(c_name) :: nil)
      | Some (clk_id, rst_id) =>
          match find_method Ids.step c.(c_methods),
                find_method Ids.reset c.(c_methods)
          with
          | Some stepm, Some resetm =>
              match get_mappings_from_node stepm.(m_in) env,
                    get_mappings_from_node stepm.(m_out) env,
                    get_mappings_from_node stepm.(m_vars) env,
                    get_mappings_from_node c.(c_mems) env,
                    SIG.find_signature c.(c_name) G,
                    SECOBCTYPING.generate_state_env c.(c_objs) SC.init_state
              with
              | Some inp_ids,
                Some out_ids,
                Some local_ids,
                Some mem_ids,
                Some sig,
                OK ((state_env, _), st_state) =>
                  match SECOBCTYPING.generate_stmt_constraints
                          G env state_env sig.(SIG.s_reset)
                          [sig.(SIG.s_clk)]
                          stepm.(m_body) st_state
                  with
                  | Error e => Error e
                  | OK (craw_step, st_step) =>
                      match SECOBCTYPING.generate_stmt_constraints
                              G env state_env sig.(SIG.s_reset)
                              []
                              resetm.(m_body) st_step
                      with
                      | Error e => Error e
                      | OK (craw_reset, _) =>
                          match build_state_instance_dump
                                  c.(c_name) c.(c_objs) state_env
                          with
                          | Error e => Error e
                          | OK state_ids =>
                              OK {| obc_dump_name := c.(c_name);
                                    obc_dump_clk := sig.(SIG.s_clk);
                                    obc_dump_rst := sig.(SIG.s_reset);
                                    obc_dump_inputs :=
                                      zip_idents (map fst stepm.(m_in)) inp_ids;
                                    obc_dump_outputs :=
                                      zip_idents (map fst stepm.(m_out)) out_ids;
                                    obc_dump_locals :=
                                      zip_idents (map fst stepm.(m_vars)) local_ids;
                                    obc_dump_mems :=
                                      zip_idents (map fst c.(c_mems)) mem_ids;
                                    obc_dump_state_instances := state_ids;
                                    obc_dump_raw_constraints :=
                                      craw_step ++ craw_reset;
                                    obc_dump_collapsed_constraints :=
                                      SymTypes.collapse (craw_step ++ craw_reset);
                                    obc_dump_constraints := sig.(SIG.s_constraints) |}
                          end
                      end
                  end
              | None, _, _, _, _, _ =>
                  Error (MSG "Missing generated input mappings for class "
                         :: CTX c.(c_name) :: nil)
              | _, None, _, _, _, _ =>
                  Error (MSG "Missing generated output mappings for class "
                         :: CTX c.(c_name) :: nil)
              | _, _, None, _, _, _ =>
                  Error (MSG "Missing generated local mappings for class "
                         :: CTX c.(c_name) :: nil)
              | _, _, _, None, _, _ =>
                  Error (MSG "Missing generated memory mappings for class "
                         :: CTX c.(c_name) :: nil)
              | _, _, _, _, None, _ =>
                  Error (MSG "Missing generated security signature for class "
                         :: CTX c.(c_name) :: nil)
              | _, _, _, _, _, Error e =>
                  Error e
              end
          | None, _ =>
              Error (MSG "Missing step method for class "
                     :: CTX c.(c_name) :: nil)
          | _, None =>
              Error (MSG "Missing reset method for class "
                     :: CTX c.(c_name) :: nil)
          end
      end
  end.

Fixpoint build_constraint_dump
  (classes : SynObc.program)
  (envs : node_scoped_env)
  (aux_names : list node_aux_names)
  (G : SIG.secglobal)
  : res obc_constraint_dump :=
  match classes with
  | [] => OK []
  | c :: classes' =>
      match build_class_constraint_dump envs aux_names G c with
      | Error e => Error e
      | OK d =>
          match build_constraint_dump classes' envs aux_names G with
          | Error e => Error e
          | OK ds => OK (d :: ds)
          end
      end
  end.

(** The Obc program the compiler emits is [Stc2Obc.translate] of the
    *scheduled* Stc program, not of [NL2Stc.translate nodes].  Those are
    different programs -- the step method's statements are in a different
    order -- so the dump has to be given the scheduled systems rather
    than recompute the pipeline.  It cannot schedule for itself:
    [Scheduler] is realised in [NLCorrectness], above this file in the
    dependency order.

    The Stc dump next door stays at the *unscheduled* program on purpose:
    that is the one the NLustre-to-Stc bridge proves about.  B4
    ([generated_signatures_preserved_by_scheduling]) is what relates the
    two, so each dump sits at the point its own theorem is stated. *)

Definition generate_obc_constraint_dump
  (nodes : NL.Syn.global) (systems : Stc.Syn.program)
  : res obc_constraint_dump :=

  let ordered_nodes := rev nodes in
  let classes := Instantiator.Stc2Obc.translate systems in
  match NAMEGEN.generate_node_scoped_env ordered_nodes with
  | Error e => Error e
  | OK (envs, aux_names) =>
      match SECOBCTYPING.generate_all_class_signatures_scoped_env classes envs aux_names with
      | Error e => Error e
      | OK G => build_constraint_dump classes envs aux_names G
      end
  end.
