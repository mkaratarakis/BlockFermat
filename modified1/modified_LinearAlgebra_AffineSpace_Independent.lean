def AffineIndependent (p : ι → P) : Prop :=
  ∀ (s : Finset ι) (w : ι → k),
    ∑ i in s, w i = 0 → s.weightedVSub p w = (0 : V) → ∀ i ∈ s, w i = 0
#align affine_independent AffineIndependent

def (p : ι → P) :
    AffineIndependent k p ↔
      ∀ (s : Finset ι) (w : ι → k),
        ∑ i in s, w i = 0 → s.weightedVSub p w = (0 : V) → ∀ i ∈ s, w i = 0 :=
  Iff.rfl
#align affine_independent_def affineIndependent_def

def
      let s2 : Finset ι := insert i1 (s.map (Embedding.subtype _))
      have hfg : ∀ x : { x // x ≠ i1 }, g x = f x := by
        intro x
        rw [hfdef]
        dsimp only
        erw [dif_neg x.property, Subtype.coe_eta]
      rw [hfg]
      have hf : ∑ ι in s2, f ι = 0 := by
        rw [Finset.sum_insert
            (Finset.not_mem_map_subtype_of_not_property s (Classical.not_not.2 rfl)),
          Finset.sum_subtype_map_embedding fun x _ => (hfg x).symm]
        rw [hfdef]
        dsimp only
        rw [dif_pos rfl]
        exact neg_add_self _
      have hs2 : s2.weightedVSub p f = (0 : V) := by
        set f2 : ι → V := fun x => f x • (p x -ᵥ p i1) with hf2def
        set g2 : { x // x ≠ i1 } → V := fun x => g x • (p x -ᵥ p i1)
        have hf2g2 : ∀ x : { x // x ≠ i1 }, f2 x = g2 x := by
          simp only [g2, hf2def]
          refine' fun x => _
          rw [hfg]
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s2 f p hf (p i1),
          Finset.weightedVSubOfPoint_insert, Finset.weightedVSubOfPoint_apply,
          Finset.sum_subtype_map_embedding fun x _ => hf2g2 x]
        exact hg
      exact h s2 f hf hs2 i (Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨i, hi, rfl⟩))
    · intro h
      rw [linearIndependent_iff'] at h
      intro s w hw hs i hi
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w p hw (p i1), ←
        s.weightedVSubOfPoint_erase w p i1, Finset.weightedVSubOfPoint_apply] at hs
      let f : ι → V := fun i => w i • (p i -ᵥ p i1)
      have hs2 : (∑ i in (s.erase i1).subtype fun i => i ≠ i1, f i) = 0 := by
        rw [← hs]
        convert Finset.sum_subtype_of_mem f fun x => Finset.ne_of_mem_erase
      have h2 := h ((s.erase i1).subtype fun i => i ≠ i1) (fun x => w x) hs2
      simp_rw [Finset.mem_subtype] at h2
      have h2b : ∀ i ∈ s, i ≠ i1 → w i = 0 := fun i his hi =>
        h2 ⟨i, hi⟩ (Finset.mem_erase_of_ne_of_mem hi his)
      exact Finset.eq_zero_of_sum_eq_zero hw h2b i hi
#align affine_independent_iff_linear_independent_vsub affineIndependent_iff_linearIndependent_vsub

def mkOfPoint (p : P) : Simplex k P 0 :=
  have : Subsingleton (Fin (1 + 0)) := by rw [add_zero]; infer_instance
  ⟨fun _ => p, affineIndependent_of_subsingleton k _⟩
#align affine.simplex.mk_of_point Affine.Simplex.mkOfPoint

def face {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ} (h : fs.card = m + 1) :
    Simplex k P m :=
  ⟨s.points ∘ fs.orderEmbOfFin h, s.independent.comp_embedding (fs.orderEmbOfFin h).toEmbedding⟩
#align affine.simplex.face Affine.Simplex.face

def reindex {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : Simplex k P n :=
  ⟨s.points ∘ e.symm, (affineIndependent_equiv e.symm).2 s.independent⟩
#align affine.simplex.reindex Affine.Simplex.reindex

structure Simplex (n : ℕ) where
  points : Fin (n + 1) → P
  independent : AffineIndependent k points
#align affine.simplex Affine.Simplex