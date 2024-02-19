
From Velus Require Import Common.
From Velus Require Import SecLattice.

From Velus Require Import NLustre.


Module Type NLusTyping
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CStr  : COINDSTREAMS    Op OpAux)
       (Import IStr  : INDEXEDSTREAMS  Op OpAux)
       (Import CIStr : COINDTOINDEXED  Op OpAux CStr IStr)
       (Import CE    : COREEXPR    Ids Op OpAux      IStr)
       (Import NL    : NLUSTRE     Ids Op OpAux CStr IStr CIStr CE).
  

End NLusTyping.
