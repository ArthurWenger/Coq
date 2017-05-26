Une tentative de modélisation d'un réseau sur [Coq 8.6](https://coq.inria.fr/) ayant pour objectif de démontrer un ensemble de proprietés sur un protocole de routage experimental.

## Contenu des fichiers

* __option.v__ : Un type inductif permettant d'éliminer les paramètres par défaut dans les définitions sur des types polymorphes.

* __region.v__ : Une définition inductive du codage de sections du réseau.

* __clist.v__ : Une formalisation de listes polymorphes et de fonctions sur des listes de régions.

* __listlist.v__ : Une définition de listes contenant d'autres listes. Les matrices sont modélisées comme un sous ensemble de ces listes.
Les matrices de régions permettent de représenter le partitionnement du plan du réseau.

* __treeRegion.v__ : Une représentation de la hiérarchie des régions (inutilisée dans le le reste du projet).

* __partition_plan.v__ : Une modélisation d'un algorithme de partitionnement du réseau sous la forme de matrices de regions.

* __network.v__ : La modélisation du réseau et des propriétés à démontrer.

### Dates et conditions de rendu

* Lundi 05 juin à 9h: rendre le code, le rapport ainsi que la presentation orale. 
* Soutenance le 5, 6 ou 7 juin l'après-midi
* Le rapport doit contenir entre 10 et 15 pages et la présentation environ 15 pages.
* Style imposé pour le rendu Latex: beamer.

