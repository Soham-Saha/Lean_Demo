-- # Formalizing https://math.stackexchange.com/a/5015161

-- # Author: Soham Saha (https://math.stackexchange.com/users/1203597/soham-saha)


/-
Note to future-self:

  First think the most basic thing you need at the next step. Then think which basic hypotheses (that you have now) are needed to prove it.
  Then set up:
    have H:<what I need>:=by
      apply? using <what things I think are basic and enough to get what I need, seperated by comma>
      
  Also rw? can be used. See https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Proving.20a*b.3Dc*b.20.3D.3E.20a.3Dc.20for.20a.2Cb.2Cc.20in.20PNat.3F$0
-/

import Mathlib

def oneIsNItself (f:ℕ+ → ℕ+)(k:ℕ+):Prop:=(k>1 → ∃d,f k+f d=k ∧ d∣k ∧ d≠k)

theorem MSEQuestionProof (f:ℕ+ → ℕ+) (h_1:∀n,n>1 → (∃d1 d2,f d1+f d2=n ∧ d1∣n ∧ d2∣n ∧ d1≠d2)) (h_2:f 1=1):∀n,oneIsNItself f n:= by
  have interim:(∀m, (∀m1 < m,oneIsNItself f m1) → oneIsNItself f m):=by
    intro m2
    intro h2
    intro h3
    by_cases h4:PNat.Prime m2
    . apply h_1 at h3
      cases h3
      rename_i d1 h5
      cases h5
      rename_i d2 h6
      have h7:=h6.right.right.right
      have h8:d1=1∨d1=m2:=by 
        rw [←PNat.dvd_prime h4]
        exact h6.right.left
      have h9:d2=1∨d2=m2:=by 
        rw [←PNat.dvd_prime h4]
        exact h6.right.right.left
      cases h8
      . rename_i h10
        rw [h10] at h7
        simp at h7
        rw [eq_comm] at h7
        have h11:=Or.resolve_left h9 h7
        have h12:=h6.left
        rw [h10, h11, add_comm] at h12
        exists 1
        simp
        nth_rw 2 [eq_comm]
        exact And.intro h12 (PNat.Prime.ne_one h4)
      . rename_i h10
        rw [h10] at h7
        simp at h7
        rw [eq_comm] at h7
        have h11:=Or.resolve_right h9 h7
        have h12:=h6.left
        rw [h10, h11] at h12
        exists 1
        simp
        nth_rw 2 [eq_comm]
        exact And.intro h12 (PNat.Prime.ne_one h4)
    . have h5:=h3
      apply h_1 at h5
      cases h5
      rename_i d1 h6
      cases h6
      rename_i d2 h7
      by_cases h8:(d1=m2 ∨ d2=m2)
      . cases h8
        . rename_i H
          rw [H] at h7
          simp at h7
          nth_rw 2 [eq_comm] at h7
          exists d2
        . rename_i H
          rw [H] at h7
          simp at h7
          rw [add_comm] at h7
          exists d1
      . rw [not_or] at h8
        have h9:=lt_of_le_of_ne (PNat.le_of_dvd  h7.right.right.left) h8.right
        have h10:=lt_of_le_of_ne (PNat.le_of_dvd  h7.right.left) h8.left
        have h11:=h9
        have h12:=h10
        apply h2 at h11
        apply h2 at h12
        have h13:f d1≤d1:=by
          by_cases h14:d1=1
          . rw [←h14] at h_2
            exact le_of_eq h_2
          . rw [eq_comm] at h14
            have h15:=h12 (lt_of_le_of_ne (PNat.one_le d1) h14)
            cases h15
            rename_i d h16
            have h17:=h16.left
            have h18:= add_le_add_right (PNat.one_le (f d)) (f d1)
            nth_rw 2 [add_comm] at h18
            rw [h17,add_comm] at h18
            exact le_of_lt h18
        have h14:f d2≤d2:=by
          by_cases h14:d2=1
          . rw [←h14] at h_2
            exact le_of_eq h_2
          . rw [eq_comm] at h14
            have h15:=h11 (lt_of_le_of_ne (PNat.one_le d2) h14)
            cases h15
            rename_i d h16
            have h17:=h16.left
            have h18:= add_le_add_right (PNat.one_le (f d)) (f d2)
            nth_rw 2 [add_comm] at h18
            rw [h17,add_comm] at h18
            exact le_of_lt h18
        have h15:= add_le_add h13 h14
        rw [h7.left] at h15
        have h16:=exists_eq_mul_left_of_dvd h7.right.left
        have h17:=exists_eq_mul_left_of_dvd h7.right.right.left
        cases h16
        rename_i c1 h18
        cases h17
        rename_i c2 h19
        by_cases h20:c1≤1
        . apply PNat.le_one_iff.mp at h20
          rw [h20] at h18
          simp at h18
          have h21:=h8.left
          rw [eq_comm] at h18
          contradiction
        . by_cases h21:c2≤1
          . apply PNat.le_one_iff.mp at h21
            rw [h21] at h19
            simp at h19
            have h22:=h8.right
            rw [eq_comm] at h19
            contradiction
          . apply lt_of_not_ge at h20
            apply lt_of_not_ge at h21
            by_cases h22:c1≤2
            . have h23:=le_antisymm h22 h20
              by_cases h24:c2≤2
              . have h25:=le_antisymm h24 h21
                rw [h23] at h18
                rw [h25] at h19
                rw [h18] at h19
                rw [mul_left_cancel_iff] at h19
                have h26:=h7.right.right.right
                contradiction
              . rw [←mul_le_mul_iff_right 2] at h15
                have h25:m2*2=m2+m2:=by
                  have H:m2*2=m2*(1+1):=rfl
                  rw[H, mul_add]
                  simp
                nth_rw 1 [h25, h18, h19, h23, mul_comm, add_mul, add_le_add_iff_left, mul_comm, mul_le_mul_iff_left] at h15
                contradiction
            . rw [←mul_le_mul_iff_left 3,mul_add] at h15
              have h23:3≤c1:=lt_of_not_ge h22
              rw [mul_comm] at h18
              rw [←mul_le_mul_iff_left d1,mul_comm,←add_le_add_iff_right (3*d2),←h18] at h23
              apply (Preorder.le_trans (3*m2) (3*d1+3*d2) (m2+3*d2) h15) at h23
              have h24:3*m2=(2+1)*m2:=rfl
              have h25:2≤c2:=h21
              rw[h24,add_mul] at h23
              simp at h23
              nth_rewrite 1 [add_comm] at h23
              rw[add_le_add_iff_left m2,h19,←mul_assoc,mul_le_mul_iff_right d2] at h23
              rw[←mul_le_mul_iff_right 2] at h25
              rw[mul_comm c2 2] at h25
              apply (Preorder.le_trans (2*2) (2*c2) 3 h25) at h23
              contradiction
  intro n2
  exact PNat.strongInductionOn n2 interim
