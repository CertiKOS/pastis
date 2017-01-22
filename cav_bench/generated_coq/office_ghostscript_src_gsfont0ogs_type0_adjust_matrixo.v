Require Import pasta.Pasta.

Notation IDgs_type0_adjust_matrix_z := 1%positive.
Notation IDgs_type0_adjust_matrix__tmp := 2%positive.
Notation IDgs_type0_adjust_matrix_code := 3%positive.
Notation IDgs_type0_adjust_matrix_fdep_size := 4%positive.
Notation IDgs_type0_adjust_matrix_i := 5%positive.
Notation IDgs_type0_adjust_matrix_pfont_dref_off280_off56 := 6%positive.
Notation IDgs_type0_adjust_matrix_pdir := 7%positive.
Notation IDgs_type0_adjust_matrix_pfont := 8%positive.
Notation IDgs_type0_adjust_matrix_pmat := 9%positive.
Definition gs_type0_adjust_matrix : graph := {|
  g_start := 1%positive;
  g_end := 55%positive;
  g_edges := (1%positive,(AAssign IDgs_type0_adjust_matrix_z
             (Some (ENum (0)))),2%positive)::
             (2%positive,(AGuard
             (fun s => ((eval (EVar IDgs_type0_adjust_matrix_i) s) >=
             (eval (ENum (0)) s))%Z)),3%positive)::
             (3%positive,(AGuard
             (fun s => ((eval (EVar IDgs_type0_adjust_matrix_fdep_size) s) >=
             (eval (ENum (0)) s))%Z)),4%positive)::
             (4%positive,AWeaken,5%positive)::
             (5%positive,(AAssign IDgs_type0_adjust_matrix_fdep_size
             (Some (EVar IDgs_type0_adjust_matrix_pfont_dref_off280_off56))),
             6%positive)::
             (6%positive,(AAssign IDgs_type0_adjust_matrix_i
             (Some (ENum (0)))),7%positive)::(7%positive,ANone,8%positive)::
             (8%positive,AWeaken,9%positive)::
             (9%positive,(AGuard
             (fun s => ((eval (EVar IDgs_type0_adjust_matrix_i) s) <
             (eval (EVar IDgs_type0_adjust_matrix_fdep_size) s))%Z)),
             11%positive)::
             (9%positive,(AGuard
             (fun s => ((eval (EVar IDgs_type0_adjust_matrix_i) s) >=
             (eval (EVar IDgs_type0_adjust_matrix_fdep_size) s))%Z)),
             10%positive)::(10%positive,AWeaken,21%positive)::
             (11%positive,AWeaken,12%positive)::
             (12%positive,ANone,19%positive)::
             (12%positive,ANone,13%positive)::
             (13%positive,ANone,14%positive)::
             (14%positive,(AAssign IDgs_type0_adjust_matrix_i
             (Some (EAdd (EVar IDgs_type0_adjust_matrix_i) (ENum (1))))),
             15%positive)::(15%positive,ANone,16%positive)::
             (16%positive,ANone,17%positive)::
             (17%positive,(AAssign IDgs_type0_adjust_matrix_z
             (Some (EAdd (ENum (1)) (EVar IDgs_type0_adjust_matrix_z)))),
             18%positive)::(18%positive,AWeaken,9%positive)::
             (19%positive,ANone,20%positive)::
             (20%positive,AWeaken,21%positive)::
             (21%positive,(AGuard
             (fun s => ((eval (EVar IDgs_type0_adjust_matrix_i) s) =
             (eval (EVar IDgs_type0_adjust_matrix_fdep_size) s))%Z)),
             51%positive)::
             (21%positive,(AGuard
             (fun s => ((eval (EVar IDgs_type0_adjust_matrix_i) s) <>
             (eval (EVar IDgs_type0_adjust_matrix_fdep_size) s))%Z)),
             22%positive)::(22%positive,AWeaken,23%positive)::
             (23%positive,ANone,48%positive)::
             (23%positive,ANone,24%positive)::
             (24%positive,ANone,25%positive)::
             (25%positive,AWeaken,26%positive)::
             (26%positive,(AGuard
             (fun s => ((eval (EVar IDgs_type0_adjust_matrix_i) s) <
             (eval (EVar IDgs_type0_adjust_matrix_fdep_size) s))%Z)),
             31%positive)::
             (26%positive,(AGuard
             (fun s => ((eval (EVar IDgs_type0_adjust_matrix_i) s) >=
             (eval (EVar IDgs_type0_adjust_matrix_fdep_size) s))%Z)),
             27%positive)::(27%positive,AWeaken,28%positive)::
             (28%positive,(AAssign IDgs_type0_adjust_matrix__tmp
             (Some (ENum (0)))),29%positive)::
             (29%positive,ANone,30%positive)::
             (30%positive,AWeaken,55%positive)::
             (31%positive,AWeaken,32%positive)::
             (32%positive,ANone,33%positive)::
             (32%positive,ANone,38%positive)::
             (33%positive,(AAssign IDgs_type0_adjust_matrix_code None),
             34%positive)::(34%positive,AWeaken,35%positive)::
             (35%positive,(AGuard
             (fun s => ((eval (EVar IDgs_type0_adjust_matrix_code) s) <
             (eval (ENum (0)) s))%Z)),44%positive)::
             (35%positive,(AGuard
             (fun s => ((eval (EVar IDgs_type0_adjust_matrix_code) s) >=
             (eval (ENum (0)) s))%Z)),36%positive)::
             (36%positive,AWeaken,37%positive)::
             (37%positive,ANone,38%positive)::
             (38%positive,ANone,39%positive)::
             (39%positive,(AAssign IDgs_type0_adjust_matrix_i
             (Some (EAdd (EVar IDgs_type0_adjust_matrix_i) (ENum (1))))),
             40%positive)::(40%positive,ANone,41%positive)::
             (41%positive,ANone,42%positive)::
             (42%positive,(AAssign IDgs_type0_adjust_matrix_z
             (Some (EAdd (ENum (1)) (EVar IDgs_type0_adjust_matrix_z)))),
             43%positive)::(43%positive,AWeaken,26%positive)::
             (44%positive,AWeaken,45%positive)::
             (45%positive,(AAssign IDgs_type0_adjust_matrix__tmp
             (Some (EVar IDgs_type0_adjust_matrix_code))),46%positive)::
             (46%positive,ANone,47%positive)::
             (47%positive,AWeaken,55%positive)::
             (48%positive,(AAssign IDgs_type0_adjust_matrix__tmp
             (Some (ENum (-25)))),49%positive)::
             (49%positive,ANone,50%positive)::
             (50%positive,AWeaken,55%positive)::
             (51%positive,AWeaken,52%positive)::
             (52%positive,(AAssign IDgs_type0_adjust_matrix__tmp
             (Some (ENum (0)))),53%positive)::
             (53%positive,ANone,54%positive)::
             (54%positive,AWeaken,55%positive)::nil
|}.

Definition gs_type0_adjust_matrix_ai (p: node) (s: state) := 
  match p with
    | 1%positive => (True)%Z
    | 2%positive => (1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0)%Z
    | 3%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 4%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size) <= 0)%Z
    | 5%positive => (-1 * (s IDgs_type0_adjust_matrix_fdep_size) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 6%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0)%Z
    | 7%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 8%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0)%Z
    | 9%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 10%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_fdep_size)+ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 11%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0)%Z
    | 12%positive => (-1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 13%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0)%Z
    | 14%positive => (-1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 15%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0)%Z
    | 16%positive => (-1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0)%Z
    | 17%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0)%Z
    | 18%positive => (-1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) + 1 <= 0)%Z
    | 19%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0)%Z
    | 20%positive => (-1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 21%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0)%Z
    | 22%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 23%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0)%Z
    | 24%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 25%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0)%Z
    | 26%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 27%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_fdep_size)+ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 28%positive => (1 * (s IDgs_type0_adjust_matrix_fdep_size)+ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 29%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_fdep_size)+ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix__tmp) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix__tmp) <= 0)%Z
    | 30%positive => (-1 * (s IDgs_type0_adjust_matrix__tmp) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix__tmp) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_fdep_size)+ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 31%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0)%Z
    | 32%positive => (-1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 33%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0)%Z
    | 34%positive => (-1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 35%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0)%Z
    | 36%positive => (-1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_code) <= 0)%Z
    | 37%positive => (-1 * (s IDgs_type0_adjust_matrix_code) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0)%Z
    | 38%positive => (-1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 39%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0)%Z
    | 40%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 41%positive => (-1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0)%Z
    | 42%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 43%positive => (-1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) + 1 <= 0)%Z
    | 44%positive => (-1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_code) + 1 <= 0)%Z
    | 45%positive => (1 * (s IDgs_type0_adjust_matrix_code) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0)%Z
    | 46%positive => (-1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_code) + 1 <= 0 /\ 1 * (s IDgs_type0_adjust_matrix__tmp) + 1 <= 0)%Z
    | 47%positive => (1 * (s IDgs_type0_adjust_matrix__tmp) + 1 <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_code) + 1 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) + 1 <= 0)%Z
    | 48%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 49%positive => (-1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix__tmp) + 25 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix__tmp) + -25 <= 0)%Z
    | 50%positive => (-1 * (s IDgs_type0_adjust_matrix__tmp) + -25 <= 0 /\ 1 * (s IDgs_type0_adjust_matrix__tmp) + 25 <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 51%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_fdep_size)+ -1 * (s IDgs_type0_adjust_matrix_i) <= 0)%Z
    | 52%positive => (1 * (s IDgs_type0_adjust_matrix_fdep_size)+ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0)%Z
    | 53%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_fdep_size)+ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix__tmp) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix__tmp) <= 0)%Z
    | 54%positive => (-1 * (s IDgs_type0_adjust_matrix__tmp) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix__tmp) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix_fdep_size)+ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_fdep_size)+ 1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_z) <= 0)%Z
    | 55%positive => (-1 * (s IDgs_type0_adjust_matrix_z) <= 0 /\ -1 * (s IDgs_type0_adjust_matrix_i) <= 0 /\ 1 * (s IDgs_type0_adjust_matrix__tmp) <= 0)%Z
    | _ => False
  end.

Definition gs_type0_adjust_matrix_pot (p : node) (s : state): Q := 
  match p with
    | 1%positive => (max0((s IDgs_type0_adjust_matrix_pfont_dref_off280_off56)))%Q
    | 2%positive => ((s IDgs_type0_adjust_matrix_z)
                     + max0((s IDgs_type0_adjust_matrix_pfont_dref_off280_off56)))%Q
    | 3%positive => ((s IDgs_type0_adjust_matrix_z)
                     + max0((s IDgs_type0_adjust_matrix_pfont_dref_off280_off56)))%Q
    | 4%positive => ((s IDgs_type0_adjust_matrix_z)
                     + max0((s IDgs_type0_adjust_matrix_pfont_dref_off280_off56)))%Q
    | 5%positive => ((s IDgs_type0_adjust_matrix_z)
                     + max0((s IDgs_type0_adjust_matrix_pfont_dref_off280_off56)))%Q
    | 6%positive => ((s IDgs_type0_adjust_matrix_z)
                     + max0((s IDgs_type0_adjust_matrix_fdep_size)))%Q
    | 7%positive => ((s IDgs_type0_adjust_matrix_z)
                     + max0((s IDgs_type0_adjust_matrix_fdep_size)
                            - (s IDgs_type0_adjust_matrix_i)))%Q
    | 8%positive => ((s IDgs_type0_adjust_matrix_z)
                     + max0((s IDgs_type0_adjust_matrix_fdep_size)
                            - (s IDgs_type0_adjust_matrix_i)))%Q
    | 9%positive => ((s IDgs_type0_adjust_matrix_z)
                     + max0((s IDgs_type0_adjust_matrix_fdep_size)
                            - (s IDgs_type0_adjust_matrix_i)))%Q
    | 10%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 11%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 12%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 13%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 14%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 15%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 16%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 17%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 18%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 19%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 20%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 21%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 22%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 23%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 24%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 25%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 26%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 27%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 28%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 29%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 30%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 31%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 32%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 33%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 34%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 35%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 36%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 37%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 38%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 39%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 40%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 41%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 42%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 43%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 44%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 45%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 46%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 47%positive => ((1 # 1) + (s IDgs_type0_adjust_matrix_z)
                      + max0(-1 + (s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 48%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 49%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 50%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 51%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 52%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 53%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 54%positive => ((s IDgs_type0_adjust_matrix_z)
                      + max0((s IDgs_type0_adjust_matrix_fdep_size)
                             - (s IDgs_type0_adjust_matrix_i)))%Q
    | 55%positive => ((s IDgs_type0_adjust_matrix_z))%Q
    | _ => (0 # 1)%Q
  end.

Definition gs_type0_adjust_matrix_hints (p : node) (s : state) := 
  match p with
    | 1%positive => []
    | 2%positive => []
    | 3%positive => []
    | 4%positive => []
    | 5%positive => []
    | 6%positive => []
    | 7%positive => []
    | 8%positive => []
    | 9%positive => []
    | 10%positive => []
    | 11%positive => [(*0 1*) F_max0_pre_decrement ((s IDgs_type0_adjust_matrix_fdep_size)
                                                    - (s IDgs_type0_adjust_matrix_i)) (1)]
    | 12%positive => []
    | 13%positive => []
    | 14%positive => []
    | 15%positive => []
    | 16%positive => []
    | 17%positive => []
    | 18%positive => []
    | 19%positive => []
    | 20%positive => [(*-1 0*) F_binom_monotonic 1 (F_max0_le_arg (F_check_ge ((s IDgs_type0_adjust_matrix_fdep_size)
                                                                    - (s IDgs_type0_adjust_matrix_i)) (0))) (F_max0_ge_0 ((s IDgs_type0_adjust_matrix_fdep_size)
                                                                    - (s IDgs_type0_adjust_matrix_i)));
                      (*-1 0*) F_binom_monotonic 1 (F_max0_ge_arg (-1
                                                                   + 
                                                                   (s IDgs_type0_adjust_matrix_fdep_size)
                                                                   - 
                                                                   (s IDgs_type0_adjust_matrix_i))) (F_check_ge (-1
                                                                    + (s IDgs_type0_adjust_matrix_fdep_size)
                                                                    - (s IDgs_type0_adjust_matrix_i)) (0))]
    | 21%positive => []
    | 22%positive => []
    | 23%positive => []
    | 24%positive => []
    | 25%positive => []
    | 26%positive => []
    | 27%positive => []
    | 28%positive => []
    | 29%positive => []
    | 30%positive => [(*-1 0*) F_max0_monotonic (F_check_ge ((s IDgs_type0_adjust_matrix_fdep_size)
                                                             - (s IDgs_type0_adjust_matrix_i)) (-1
                                                                    + (s IDgs_type0_adjust_matrix_fdep_size)
                                                                    - (s IDgs_type0_adjust_matrix_i)));
                      (*-1 0*) F_max0_ge_0 (-1
                                            + (s IDgs_type0_adjust_matrix_fdep_size)
                                            - (s IDgs_type0_adjust_matrix_i))]
    | 31%positive => [(*-1 0*) F_max0_pre_decrement ((s IDgs_type0_adjust_matrix_fdep_size)
                                                     - (s IDgs_type0_adjust_matrix_i)) (1)]
    | 32%positive => []
    | 33%positive => []
    | 34%positive => []
    | 35%positive => []
    | 36%positive => []
    | 37%positive => []
    | 38%positive => []
    | 39%positive => []
    | 40%positive => []
    | 41%positive => []
    | 42%positive => []
    | 43%positive => []
    | 44%positive => []
    | 45%positive => []
    | 46%positive => []
    | 47%positive => [(*-1 0*) F_one;
                      (*-1 0*) F_max0_ge_0 (-1
                                            + (s IDgs_type0_adjust_matrix_fdep_size)
                                            - (s IDgs_type0_adjust_matrix_i))]
    | 48%positive => []
    | 49%positive => []
    | 50%positive => [(*-1 0*) F_max0_monotonic (F_check_ge ((s IDgs_type0_adjust_matrix_fdep_size)
                                                             - (s IDgs_type0_adjust_matrix_i)) (-1
                                                                    + (s IDgs_type0_adjust_matrix_fdep_size)
                                                                    - (s IDgs_type0_adjust_matrix_i)));
                      (*-1 0*) F_max0_ge_0 (-1
                                            + (s IDgs_type0_adjust_matrix_fdep_size)
                                            - (s IDgs_type0_adjust_matrix_i))]
    | 51%positive => []
    | 52%positive => []
    | 53%positive => []
    | 54%positive => [(*-1 0*) F_max0_monotonic (F_check_ge ((s IDgs_type0_adjust_matrix_fdep_size)
                                                             - (s IDgs_type0_adjust_matrix_i)) (-1
                                                                    + (s IDgs_type0_adjust_matrix_fdep_size)
                                                                    - (s IDgs_type0_adjust_matrix_i)));
                      (*-1 0*) F_max0_ge_0 (-1
                                            + (s IDgs_type0_adjust_matrix_fdep_size)
                                            - (s IDgs_type0_adjust_matrix_i))]
    | 55%positive => []
    | _ => []
  end.


Theorem gs_type0_adjust_matrix_ai_correct:
  forall s p' s', steps (g_start gs_type0_adjust_matrix) s (g_edges gs_type0_adjust_matrix) p' s' -> gs_type0_adjust_matrix_ai p' s'.
Proof.
  check_ai.
Qed.

Theorem gs_type0_adjust_matrix_pot_correct:
  forall s p' s',
    steps (g_start gs_type0_adjust_matrix) s (g_edges gs_type0_adjust_matrix) p' s' ->
    (gs_type0_adjust_matrix_pot (g_start gs_type0_adjust_matrix) s >= gs_type0_adjust_matrix_pot p' s')%Q.
Proof.
  check_lp gs_type0_adjust_matrix_ai_correct gs_type0_adjust_matrix_hints.
Qed.

