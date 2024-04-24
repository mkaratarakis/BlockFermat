def splitLower (I : Box ι) (i : ι) (x : ℝ) : WithBot (Box ι) :=
  mk' I.lower (update I.upper i (min x (I.upper i)))
#align box_integral.box.split_lower BoxIntegral.Box.splitLower

def [DecidableEq ι] {i x} (h : x ∈ Ioo (I.lower i) (I.upper i))
    (h' : ∀ j, I.lower j < update I.upper i x j :=
      (forall_update_iff I.upper fun j y => I.lower j < y).2
        ⟨h.1, fun j _ => I.lower_lt_upper _⟩) :
    I.splitLower i x = (⟨I.lower, update I.upper i x, h'⟩ : Box ι) := by
  simp (config := { unfoldPartialApp := true }) only [splitLower, mk'_eq_coe, min_eq_left h.2.le,
    update, and_self]
#align box_integral.box.split_lower_def BoxIntegral.Box.splitLower_def

def splitUpper (I : Box ι) (i : ι) (x : ℝ) : WithBot (Box ι) :=
  mk' (update I.lower i (max x (I.lower i))) I.upper
#align box_integral.box.split_upper BoxIntegral.Box.splitUpper

def [DecidableEq ι] {i x} (h : x ∈ Ioo (I.lower i) (I.upper i))
    (h' : ∀ j, update I.lower i x j < I.upper j :=
      (forall_update_iff I.lower fun j y => y < I.upper j).2
        ⟨h.2, fun j _ => I.lower_lt_upper _⟩) :
    I.splitUpper i x = (⟨update I.lower i x, I.upper, h'⟩ : Box ι) := by
  simp (config := { unfoldPartialApp := true }) only [splitUpper, mk'_eq_coe, max_eq_left h.1.le,
    update, and_self]
#align box_integral.box.split_upper_def BoxIntegral.Box.splitUpper_def

def split (I : Box ι) (i : ι) (x : ℝ) : Prepartition I :=
  ofWithBot {I.splitLower i x, I.splitUpper i x}
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro J (rfl | rfl)
      exacts [Box.splitLower_le, Box.splitUpper_le])
    (by
      simp only [Finset.coe_insert, Finset.coe_singleton, true_and_iff, Set.mem_singleton_iff,
        pairwise_insert_of_symmetric symmetric_disjoint, pairwise_singleton]
      rintro J rfl -
      exact I.disjoint_splitLower_splitUpper i x)
#align box_integral.prepartition.split BoxIntegral.Prepartition.split

def splitMany (I : Box ι) (s : Finset (ι × ℝ)) : Prepartition I :=
  s.inf fun p => split I p.1 p.2
#align box_integral.prepartition.split_many BoxIntegral.Prepartition.splitMany

def compl (π : Prepartition I) : Prepartition I :=
  π.exists_iUnion_eq_diff.choose
#align box_integral.prepartition.compl BoxIntegral.Prepartition.compl