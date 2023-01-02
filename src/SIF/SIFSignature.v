(*Describes security signature related properties.*)
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import SIF.Helpers.
From Velus Require Import SIF.SymTypes. 


(*
    Given a node with input variables: x,y and output: z in the node signature
    Say n_in: [α_1,α_2], n_out:= [β], 
    we always asssume x has type α_1, y has type α_2 and z has type β
    Constraints can be in any order!
*)
Record signature := mkSig {
    n_name : ident; (*node name*)
    n_in  : list ident; (*ordered list of input security types*)
    n_out : list ident; (*ordered list of output security types*)

    n_clk : ident; (*The base clock is always empty list*)
    consraints : list constraint; (*constraints*)
}.

