(** Executable export of generated STC security signatures and constraints. *)

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import ObcToClight.Interface.
From Velus Require Import Instantiator.
From Velus Require Import Ident.
From Velus Require Import SIF.NameInterface.
From Velus Require Import SIF.SecContext.
From Velus Require Import SIF.SIFSignature.
From Velus Require Import SIF.SecCETyping.
From Velus Require Import SIF.SecSTCTyping.

From Coq Require Import String List.
From compcert Require Import common.Errors.

Import ListNotations.

Module Import Ids := Ident.Ids.
Module Import Op := Interface.Op.
Module CE := Instantiator.CE.
Module NL := Instantiator.NL.
Module Stc := Instantiator.Stc.
Module Import SynStc := Stc.Syn.

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
Module SECSTCTYPING :=
  SecSTCTyping
    Ids Op SC CE.Syn Stc.Syn SIG SECCETYPING
    CE.IsF CE.Clo Stc.Last Stc.Var Stc.Def Stc.Syst Stc.Ord Stc.Free Stc.Clo.

Record system_constraint_dump := mkSystemConstraintDump {
  stc_dump_name : ident;
  stc_dump_clk : ident;
  stc_dump_rst : ident;
  stc_dump_inputs : list (ident * ident);
  stc_dump_outputs : list (ident * ident);
  stc_dump_locals : list (ident * ident);
  stc_dump_lasts : list (ident * ident);
  stc_dump_reset_instances : list (ident * ident);
  stc_dump_raw_constraints : list SymTypes.constraint;
  stc_dump_constraints : list SymTypes.constraint
}.

Definition stc_constraint_dump := list system_constraint_dump.

Fixpoint zip_idents (xs ys : list ident) : list (ident * ident) :=
  match xs, ys with
  | x :: xs', y :: ys' => (x, y) :: zip_idents xs' ys'
  | _, _ => []
  end.

Fixpoint build_reset_instance_dump
  (sys_name : ident)
  (tcs : list trconstr)
  (reset_env : Env.t ident)
  : res (list (ident * ident)) :=
  match tcs with
  | [] => OK []
  | TcReset inst _ _ :: tcs' =>
      match Env.find inst reset_env with
      | None =>
          Error (MSG "Missing generated reset-instance mapping for system "
                 :: CTX sys_name
                 :: MSG " and subinstance "
                 :: CTX inst
                 :: nil)
      | Some rid =>
          match build_reset_instance_dump sys_name tcs' reset_env with
          | Error e => Error e
          | OK ds => OK ((inst, rid) :: ds)
          end
      end
  | _ :: tcs' =>
      build_reset_instance_dump sys_name tcs' reset_env
  end.

Definition build_system_constraint_dump
  (envs : node_scoped_env)
  (aux_names : list node_aux_names)
  (G : SIG.secglobal)
  (s : system)
  : res system_constraint_dump :=
  match find_node_env s.(s_name) envs with
  | None =>
      Error (MSG "Missing generated local security environment for system "
             :: CTX s.(s_name) :: nil)
  | Some env =>
      match get_node_aux s.(s_name) aux_names with
      | None =>
          Error (MSG "Missing generated clock/reset names for system "
                 :: CTX s.(s_name) :: nil)
      | Some (clk_id, rst_id) =>
          match get_mappings_from_node s.(s_in) env,
                get_mappings_from_node s.(s_out) env,
                get_mappings_from_node s.(s_vars) env,
                get_mappings_from_node s.(s_lasts) env,
                SIG.find_signature s.(s_name) G,
                SECSTCTYPING.generate_reset_env s.(s_tcs) SC.init_state
          with
          | Some inp_ids,
            Some out_ids,
            Some local_ids,
            Some last_ids,
            Some sig,
            OK ((reset_env, _), _) =>
              match build_reset_instance_dump s.(s_name) s.(s_tcs) reset_env,
                    SECSTCTYPING.generate_trconstrs_constraints
                      G env reset_env sig.(SIG.s_clk) sig.(SIG.s_reset)
                      s.(s_tcs) SC.init_state
              with
              | OK reset_ids, OK (raw_constraints, _) =>
                  OK {| stc_dump_name := s.(s_name);
                        stc_dump_clk := sig.(SIG.s_clk);
                        stc_dump_rst := sig.(SIG.s_reset);
                        stc_dump_inputs := zip_idents (map fst s.(s_in)) inp_ids;
                        stc_dump_outputs := zip_idents (map fst s.(s_out)) out_ids;
                        stc_dump_locals := zip_idents (map fst s.(s_vars)) local_ids;
                        stc_dump_lasts := zip_idents (map fst s.(s_lasts)) last_ids;
                        stc_dump_reset_instances := reset_ids;
                        stc_dump_raw_constraints := raw_constraints;
                        stc_dump_constraints := sig.(SIG.s_constraints) |}
              | Error e, _ => Error e
              | _, Error e => Error e
              end
          | None, _, _, _, _, _ =>
              Error (MSG "Missing generated input mappings for system "
                     :: CTX s.(s_name) :: nil)
          | _, None, _, _, _, _ =>
              Error (MSG "Missing generated output mappings for system "
                     :: CTX s.(s_name) :: nil)
          | _, _, None, _, _, _ =>
              Error (MSG "Missing generated local mappings for system "
                     :: CTX s.(s_name) :: nil)
          | _, _, _, None, _, _ =>
              Error (MSG "Missing generated last mappings for system "
                     :: CTX s.(s_name) :: nil)
          | _, _, _, _, None, _ =>
              Error (MSG "Missing generated security signature for system "
                     :: CTX s.(s_name) :: nil)
          | _, _, _, _, _, Error e =>
              Error e
          end
      end
  end.

Fixpoint build_constraint_dump
  (systems : Stc.Syn.program)
  (envs : node_scoped_env)
  (aux_names : list node_aux_names)
  (G : SIG.secglobal)
  : res stc_constraint_dump :=
  match systems with
  | [] => OK []
  | s :: systems' =>
      match build_system_constraint_dump envs aux_names G s with
      | Error e => Error e
      | OK d =>
          match build_constraint_dump systems' envs aux_names G with
          | Error e => Error e
          | OK ds => OK (d :: ds)
          end
      end
  end.

Definition generate_stc_constraint_dump
  (nodes : NL.Syn.global)
  : res stc_constraint_dump :=

  let ordered_nodes := rev nodes in
  let systems := Instantiator.NL2Stc.translate ordered_nodes in
  match NAMEGEN.generate_node_scoped_env ordered_nodes with
  | Error e => Error e
  | OK (envs, aux_names) =>
      match SECSTCTYPING.generate_all_sys_signatures_scoped_env systems envs aux_names with
      | Error e => Error e
      | OK G => build_constraint_dump systems envs aux_names G
      end
  end.
