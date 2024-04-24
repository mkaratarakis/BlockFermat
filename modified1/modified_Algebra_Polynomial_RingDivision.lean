def modByMonicHom (q : R[X]) : R[X] →ₗ[R] R[X] where
  toFun p := p %ₘ q
  map_add' := add_modByMonic
  map_smul' := smul_modByMonic
#align polynomial.mod_by_monic_hom Polynomial.modByMonicHom

def roots (p : R[X]) : Multiset R :=
  haveI := Classical.decEq R
  haveI := Classical.dec (p = 0)
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)
#align polynomial.roots Polynomial.roots

def [DecidableEq R] (p : R[X]) [Decidable (p = 0)] :
    p.roots = if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h) := by
  -- porting noteL `‹_›` doesn't work for instance arguments
  rename_i iR ip0
  obtain rfl := Subsingleton.elim iR (Classical.decEq R)
  obtain rfl := Subsingleton.elim ip0 (Classical.dec (p = 0))
  rfl
#align polynomial.roots_def Polynomial.roots_def

def nthRoots (n : ℕ) (a : R) : Multiset R :=
  roots ((X : R[X]) ^ n - C a)
#align polynomial.nth_roots Polynomial.nthRoots

def nthRootsFinset (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] : Finset R :=
  haveI := Classical.decEq R
  Multiset.toFinset (nthRoots n (1 : R))
#align polynomial.nth_roots_finset Polynomial.nthRootsFinset

def (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] [DecidableEq R] :
    nthRootsFinset n R = Multiset.toFinset (nthRoots n (1 : R)) := by
  unfold nthRootsFinset
  convert rfl

@[simp]
theorem mem_nthRootsFinset {n : ℕ} (h : 0 < n) {x : R} :
    x ∈ nthRootsFinset n R ↔ x ^ (n : ℕ) = 1 := by
  classical
  rw [nthRootsFinset_def, mem_toFinset, mem_nthRoots h]
#align polynomial.mem_nth_roots_finset Polynomial.mem_nthRootsFinset

def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] :
    p.aroots S = (p.map (algebraMap T S)).roots :=
  rfl

theorem mem_aroots' [CommRing S] [IsDomain S] [Algebra T S] {p : T[X]} {a : S} :
    a ∈ p.aroots S ↔ p.map (algebraMap T S) ≠ 0 ∧ aeval a p = 0 := by
  rw [mem_roots', IsRoot.def, ← eval₂_eq_eval_map, aeval_def]

theorem mem_aroots [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {p : T[X]} {a : S} : a ∈ p.aroots S ↔ p ≠ 0 ∧ aeval a p = 0 := by
  rw [mem_aroots', Polynomial.map_ne_zero_iff]
  exact NoZeroSMulDivisors.algebraMap_injective T S

theorem aroots_mul [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {p q : T[X]} (hpq : p * q ≠ 0) :
    (p * q).aroots S = p.aroots S + q.aroots S := by
  suffices map (algebraMap T S) p * map (algebraMap T S) q ≠ 0 by
    rw [aroots_def, Polynomial.map_mul, roots_mul this]
  rwa [← Polynomial.map_mul, Polynomial.map_ne_zero_iff
    (NoZeroSMulDivisors.algebraMap_injective T S)]

@[simp]
theorem aroots_X_sub_C [CommRing S] [IsDomain S] [Algebra T S]
    (r : T) : aroots (X - C r) S = {algebraMap T S r} := by
  rw [aroots_def, Polynomial.map_sub, map_X, map_C, roots_X_sub_C]

@[simp]
theorem aroots_X [CommRing S] [IsDomain S] [Algebra T S] :
    aroots (X : T[X]) S = {0} := by
  rw [aroots_def, map_X, roots_X]

@[simp]
theorem aroots_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).aroots S = 0 := by
  rw [aroots_def, map_C, roots_C]

@[simp]
theorem aroots_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).aroots S = 0 := by
  rw [← C_0, aroots_C]

@[simp]
theorem aroots_one [CommRing S] [IsDomain S] [Algebra T S] :
    (1 : T[X]).aroots S = 0 :=
  aroots_C 1

@[simp]
theorem aroots_neg [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) :
    (-p).aroots S = p.aroots S := by
  rw [aroots, Polynomial.map_neg, roots_neg]

@[simp]
theorem aroots_C_mul [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {a : T} (p : T[X]) (ha : a ≠ 0) :
    (C a * p).aroots S = p.aroots S := by
  rw [aroots_def, Polynomial.map_mul, map_C, roots_C_mul]
  rwa [map_ne_zero_iff]
  exact NoZeroSMulDivisors.algebraMap_injective T S

@[simp]
theorem aroots_smul_nonzero [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {a : T} (p : T[X]) (ha : a ≠ 0) :
    (a • p).aroots S = p.aroots S := by
  rw [smul_eq_C_mul, aroots_C_mul _ ha]

@[simp]
theorem aroots_pow [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) (n : ℕ) :
    (p ^ n).aroots S = n • p.aroots S := by
  rw [aroots_def, Polynomial.map_pow, roots_pow]

theorem aroots_X_pow [CommRing S] [IsDomain S] [Algebra T S] (n : ℕ) :
    (X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  rw [aroots_pow, aroots_X]

theorem aroots_C_mul_X_pow [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {a : T} (ha : a ≠ 0) (n : ℕ) :
    (C a * X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  rw [aroots_C_mul _ ha, aroots_X_pow]

@[simp]
theorem aroots_monomial [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {a : T} (ha : a ≠ 0) (n : ℕ) :
    (monomial n a).aroots S = n • ({0} : Multiset S) := by
  rw [← C_mul_X_pow_eq_monomial, aroots_C_mul_X_pow ha]

/-- The set of distinct roots of `p` in `S`.

If you have a non-separable polynomial, use `Polynomial.aroots` for the multiset
where multiple roots have the appropriate multiplicity. -/
def rootSet (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Set S :=
  haveI := Classical.decEq S
  (p.aroots S).toFinset
#align polynomial.root_set Polynomial.rootSet

def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] [DecidableEq S] :
    p.rootSet S = (p.aroots S).toFinset := by
  rw [rootSet]
  convert rfl
#align polynomial.root_set_def Polynomial.rootSet_def