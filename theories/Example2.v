(* Exemple2.v

   Copyright Centre national d'études spatiales (CNES), 2023
   see LICENSE file *)

Require Import List Prelude.
(* Larger example *)
Section Example2.

Let e1 := basic 1.
Let e2 := basic 2. 
Let e3 := basic 3. 
Let e4 := basic 4. 
Let e5 := basic 5. 
Let e6 := basic 6. 
Let e7 := basic 7. 
Let e8 := basic 8. 
Let e9 := basic 9. 
Let e10 := basic 10. 
Let e11 := basic 11. 
Let e12 := basic 12. 
Let e13 := basic 13. 
Let e14 := basic 14. 
Let e15 := basic 15. 
Let e16 := basic 16. 
Let e17 := basic 17. 
Let e18 := basic 18. 
Let e19 := basic 19. 
Let e20 := basic 20. 
Let e21 := basic 21. 
Let e22 := basic 22.
Let e23 := basic 23.
Let e24 := basic 24. 
Let e25 := basic 25.

Let g35 := (e17 || e18).
Let g34 := (e19 || e20 || e21).
Let g33 := (e19 || e20).
Let g32 := (e17 || e18 || e21).
Let g31 := (g34 && g35).
Let g30 := (e24 || e25).
Let g29 := (e22 || e23).
Let g28 := (g32 && g33).
Let g27 := (e12 || e13).
Let g26 := (e9 || e10 || e11 || g31).
Let g25 := (g29 && g30).
Let g24 := (e14 || e15 || e16 || g28).
Let g23 := (e19 || e20).
Let g22 := (e17 || e18 || e21).
Let g21 := (g26 && g27).
Let g20 := (g24 && g25).
Let g19 := (e24 || e25).
Let g18 := (e22 || e23).
Let g17 := (g22 && g23).
Let g16 := (e19 || e20 || e21).
Let g15 := (e17 || e18).
Let g14 := (e4 || e5 || e6 || e7 || g21).
Let g13 := (e1 || e2 || e3 || g20).
Let g12 := (g18 && g19).
Let g11 := (e14 || e15 || e16 || g17).
Let g10 := (g15 && g16).
Let g9 := (g13 && g14).
Let top := (g11 && g12).

Import ListNotations.
Compute (mcs 5 top).

Import QArith.

Let proba := {
    (e1, 0.032),
    (e2, 0.825),
    (e3, 0.488),
    (e4, 0.503),
    (e5, 0.188),
    (e6, 0.239),
    (e7, 0.638),
    (e8, 0.506),
    (e9, 0.4810),
    (e10, 0.437),
    (e11, 0.0582),
    (e12, 0.2893),
    (e13, 0.2752),
    (e14, 0.7885),
    (e15, 0.7350),
    (e16, 0.9744),
    (e17, 0.6655),
    (e18, 0.8038),
    (e19, 0.4114),
    (e20, 0.7221),
    (e21, 0.0288),
    (e22, 0.0820),
    (e23, 0.0416),
    (e24, 0.0559),
    (e25, 0.487)
}.

Compute (tep proba top).
End Example2.
