def pred (o : Ordinal) : Ordinal :=
  if h : ∃ a, o = succ a then Classical.choose h else o
#align ordinal.pred Ordinal.pred

def IsLimit (o : Ordinal) : Prop :=
  o ≠ 0 ∧ ∀ a < o, succ a < o
#align ordinal.is_limit Ordinal.IsLimit

def limitRecOn {C : Ordinal → Sort*} (o : Ordinal) (H₁ : C 0) (H₂ : ∀ o, C o → C (succ o))
    (H₃ : ∀ o, IsLimit o → (∀ o' < o, C o') → C o) : C o :=
  lt_wf.fix
    (fun o IH =>
      if o0 : o = 0 then by rw [o0]; exact H₁
      else
        if h : ∃ a, o = succ a then by
          rw [← succ_pred_iff_is_succ.2 h]; exact H₂ _ (IH _ <| pred_lt_iff_is_succ.2 h)
        else H₃ _ ⟨o0, fun a => (succ_lt_of_not_succ h).2⟩ IH)
    o
#align ordinal.limit_rec_on Ordinal.limitRecOn

def IsNormal (f : Ordinal → Ordinal) : Prop :=
  (∀ o, f o < f (succ o)) ∧ ∀ o, IsLimit o → ∀ a, f o ≤ a ↔ ∀ b < o, f b ≤ a
#align ordinal.is_normal Ordinal.IsNormal

def (a) {b : Ordinal} (h : b ≠ 0) : a / b = sInf { o | a < b * succ o } :=
  dif_neg h
#align ordinal.div_def Ordinal.div_def

def a h]; exact csInf_mem (div_nonempty h)
#align ordinal.lt_mul_succ_div Ordinal.lt_mul_succ_div

def a b0]; exact csInf_le' h⟩
#align ordinal.div_le Ordinal.div_le

def (a b : Ordinal) : a % b = a - b * (a / b) :=
  rfl
#align ordinal.mod_def Ordinal.mod_def

def bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) :
    ∀ a < type r, α := fun a ha => f (enum r a ha)
#align ordinal.bfamily_of_family' Ordinal.bfamilyOfFamily'

def bfamilyOfFamily {ι : Type u} : (ι → α) → ∀ a < type (@WellOrderingRel ι), α :=
  bfamilyOfFamily' WellOrderingRel
#align ordinal.bfamily_of_family Ordinal.bfamilyOfFamily

def familyOfBFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀ a < o, α) : ι → α := fun i =>
  f (typein r i)
    (by
      rw [← ho]
      exact typein_lt_type r i)
#align ordinal.family_of_bfamily' Ordinal.familyOfBFamily'

def familyOfBFamily (o : Ordinal) (f : ∀ a < o, α) : o.out.α → α :=
  familyOfBFamily' (· < ·) (type_lt o) f
#align ordinal.family_of_bfamily Ordinal.familyOfBFamily

def brange (o : Ordinal) (f : ∀ a < o, α) : Set α :=
  { a | ∃ i hi, f i hi = a }
#align ordinal.brange Ordinal.brange

def sup {ι : Type u} (f : ι → Ordinal.{max u v}) : Ordinal.{max u v} :=
  iSup f
#align ordinal.sup Ordinal.sup

def bsup (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  sup.{_, v} (familyOfBFamily o f)
#align ordinal.bsup Ordinal.bsup

def lsub {ι} (f : ι → Ordinal) : Ordinal :=
  sup (succ ∘ f)
#align ordinal.lsub Ordinal.lsub

def blsub (o : Ordinal.{u}) (f : ∀ a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  bsup.{_, v} o fun a ha => succ (f a ha)
#align ordinal.blsub Ordinal.blsub

def blsub₂ (o₁ o₂ : Ordinal) (op : {a : Ordinal} → (a < o₁) → {b : Ordinal} → (b < o₂) → Ordinal) :
    Ordinal :=
  lsub (fun x : o₁.out.α × o₂.out.α => op (typein_lt_self x.1) (typein_lt_self x.2))
#align ordinal.blsub₂ Ordinal.blsub₂

def mex {ι : Type u} (f : ι → Ordinal.{max u v}) : Ordinal :=
  sInf (Set.range f)ᶜ
#align ordinal.mex Ordinal.mex

def bmex (o : Ordinal) (f : ∀ a < o, Ordinal) : Ordinal :=
  mex (familyOfBFamily o f)
#align ordinal.bmex Ordinal.bmex

def enumOrd (S : Set Ordinal.{u}) : Ordinal → Ordinal :=
  lt_wf.fix fun o f => sInf (S ∩ Set.Ici (blsub.{u, u} o f))
#align ordinal.enum_ord Ordinal.enumOrd

def (o) : enumOrd S o = sInf (S ∩ { b | ∀ c, c < o → enumOrd S c < b }) := by
  rw [enumOrd_def']
  congr; ext
  exact ⟨fun h a hao => (lt_blsub.{u, u} _ _ hao).trans_le h, blsub_le⟩
#align ordinal.enum_ord_def Ordinal.enumOrd_def

def a]
    have Hfa : f a ∈ range f ∩ { b | ∀ c, c < a → enumOrd (range f) c < b } :=
      ⟨mem_range_self a, fun b hb => by
        rw [H b hb]
        exact hf hb⟩
    refine' (csInf_le' Hfa).antisymm ((le_csInf_iff'' ⟨_, Hfa⟩).2 _)
    rintro _ ⟨⟨c, rfl⟩, hc : ∀ b < a, enumOrd (range f) b < f c⟩
    rw [hf.le_iff_le]
    contrapose! hc
    exact ⟨c, hc, (H c hc).ge⟩
#align ordinal.enum_ord_range Ordinal.enumOrd_range

def enumOrdOrderIso (hS : Unbounded (· < ·) S) : Ordinal ≃o S :=
  StrictMono.orderIsoOfSurjective (fun o => ⟨_, enumOrd_mem hS o⟩) (enumOrd_strictMono hS) fun s =>
    let ⟨a, ha⟩ := enumOrd_surjective hS s s.prop
    ⟨a, Subtype.eq ha⟩
#align ordinal.enum_ord_order_iso Ordinal.enumOrdOrderIso

def rank (h : Acc r a) : Ordinal.{u} :=
  Acc.recOn h fun a _h ih => Ordinal.sup.{u, u} fun b : { b // r b a } => Order.succ <| ih b b.2
#align acc.rank Acc.rank

def rank (a : α) : Ordinal.{u} :=
  (hwf.apply a).rank
#align well_founded.rank WellFounded.rank