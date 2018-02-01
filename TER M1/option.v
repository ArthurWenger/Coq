(* Permet d'éliminer les paramètres par défaut dans les définitions sur des types polymorphes.
   Par exemple si un élement n'est pas dans une liste de region on pourra renvoyer None plutot qu'une valeur par défaut comme Z.
   Voir [natoption] pour plus d'infos. *)
Inductive option {A:Type}: Type :=
  | Some : A -> option
  | None : option. 

(* Permet d'additioner des option de type nat sans passer par des fonctions auxiliaires. *)
Definition add_opt (a b:@option nat):@option nat :=
match a, b with
| Some a', Some b' => Some (a'+b')
| _, _ => None
end.
(* Permet d'extraire l'élement d'un type [option] et de renvoyer 
   une valeur par défaut fournie en argument dans le cas [None]. *)
Definition option_elim {A:Type} (d: A) (o: option): A :=
  match o with
  | Some n' => n'
  | None => d
  end.