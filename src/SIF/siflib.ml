open Format

let string_of_ident id =
  Camlcoq.extern_atom id

let pp_sep fmt () =
  fprintf fmt ", "

let pp_ident fmt id =
  pp_print_string fmt (string_of_ident id)

let pp_ident_list fmt ids =
  fprintf fmt "[%a]" (pp_print_list ~pp_sep pp_ident) ids

let pp_mapping fmt (src_id, sec_id) =
  fprintf fmt "%a -> %a" pp_ident src_id pp_ident sec_id

let pp_mapping_block fmt title mappings =
  fprintf fmt "  %s:@." title;
  match mappings with
  | [] ->
      fprintf fmt "    (none)@."
  | _ ->
      List.iter
        (fun mapping -> fprintf fmt "    %a@." pp_mapping mapping)
        mappings

let pp_constraint fmt (lhs, rhs) =
  fprintf fmt "    %a <= %a" pp_ident_list lhs pp_ident_list rhs

let pp_node_constraint_dump fmt dump =
  fprintf fmt "node %a@." pp_ident dump.SecNLusConstraintExport.dump_name;
  fprintf fmt "  clock: %a@." pp_ident dump.SecNLusConstraintExport.dump_clk;
  fprintf fmt "  reset: %a@." pp_ident dump.SecNLusConstraintExport.dump_rst;
  pp_mapping_block fmt "inputs" dump.SecNLusConstraintExport.dump_inputs;
  pp_mapping_block fmt "outputs" dump.SecNLusConstraintExport.dump_outputs;
  pp_mapping_block fmt "locals" dump.SecNLusConstraintExport.dump_locals;
  fprintf fmt "  raw constraints:@.";
  begin
    match dump.SecNLusConstraintExport.dump_raw_constraints with
    | [] ->
        fprintf fmt "    (none)@."
    | constraints ->
        List.iter
          (fun c -> fprintf fmt "%a@." pp_constraint c)
          constraints
  end;
  fprintf fmt "  simplified constraints:@.";
  begin
    match dump.SecNLusConstraintExport.dump_constraints with
    | [] ->
        fprintf fmt "    (none)@."
    | constraints ->
        List.iter
          (fun c -> fprintf fmt "%a@." pp_constraint c)
          constraints
  end

let print_nlustre_constraint_dump fmt dumps =
  match dumps with
  | [] ->
      fprintf fmt "(no generated NLustre security constraints)@."
  | first :: rest ->
      pp_node_constraint_dump fmt first;
      List.iter
        (fun dump ->
          fprintf fmt "@.";
          pp_node_constraint_dump fmt dump)
        rest

let pp_system_constraint_dump fmt dump =
  fprintf fmt "system %a@." pp_ident dump.SecStcConstraintExport.stc_dump_name;
  fprintf fmt "  clock: %a@." pp_ident dump.SecStcConstraintExport.stc_dump_clk;
  fprintf fmt "  reset: %a@." pp_ident dump.SecStcConstraintExport.stc_dump_rst;
  pp_mapping_block fmt "inputs" dump.SecStcConstraintExport.stc_dump_inputs;
  pp_mapping_block fmt "outputs" dump.SecStcConstraintExport.stc_dump_outputs;
  pp_mapping_block fmt "locals" dump.SecStcConstraintExport.stc_dump_locals;
  pp_mapping_block fmt "lasts" dump.SecStcConstraintExport.stc_dump_lasts;
  pp_mapping_block fmt "reset-instances" dump.SecStcConstraintExport.stc_dump_reset_instances;
  fprintf fmt "  raw constraints:@.";
  begin
    match dump.SecStcConstraintExport.stc_dump_raw_constraints with
    | [] ->
        fprintf fmt "    (none)@."
    | constraints ->
        List.iter
          (fun c -> fprintf fmt "%a@." pp_constraint c)
          constraints
  end;
  fprintf fmt "  simplified constraints:@.";
  begin
    match dump.SecStcConstraintExport.stc_dump_constraints with
    | [] ->
        fprintf fmt "    (none)@."
    | constraints ->
        List.iter
          (fun c -> fprintf fmt "%a@." pp_constraint c)
          constraints
  end

let print_stc_constraint_dump fmt dumps =
  match dumps with
  | [] ->
      fprintf fmt "(no generated STC security constraints)@."
  | first :: rest ->
      pp_system_constraint_dump fmt first;
      List.iter
        (fun dump ->
          fprintf fmt "@.";
          pp_system_constraint_dump fmt dump)
        rest
