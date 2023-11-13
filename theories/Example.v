(* Exemple.v

   Copyright Centre national d'études spatiales (CNES), 2023
   see LICENSE file *)

Require Import List Prelude.

Section Example1.

Let gps1 := basic 1.
Let gps2 := basic 2.
Let imu := basic 3.

Let lanceur := basic 4.
Let pyro1 := basic 5.
Let pyro2 := basic 6.

Let jamming := basic 7.

(* Perte de position en cas de leurrage *)
Let pos_jam := jamming && @(2,[gps1,gps2,imu]).

(* Perte de position sans leurrage *)
Let pos_nojam := gps1 && gps2 && imu.

Let pos := pos_nojam || pos_jam.

(* Perte de la pyro *)
Let pyro := pyro1 && pyro2.

(* Arbre modélisant une panne retard *)
Let top := (pos || lanceur) && pyro.

(* Permet un meilleur affichage des résultats *)
Import ListNotations.

Compute (mcs 3 top). (* Affiche tout les mcs d'ordre 3 au maximum *)


(* On importe QArith ici afin d'éviter les conflits avec les naturels *)

Import QArith.
Let proba := {
  (gps1, 0.1), 
  (gps2, 0.1), 
  (imu, 0.01),
  (lanceur, 0.5),
  (pyro1, 0.03),
  (pyro2, 0.01),
  (jamming, 0.8)
}.

Compute (tep proba top).
End Example1.
