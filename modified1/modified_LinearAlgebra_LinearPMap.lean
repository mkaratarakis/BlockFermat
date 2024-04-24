def toFun' (f : E →ₗ.[R] F) : f.domain → F := f.toFun

instance : CoeFun (E →ₗ.[R] F) fun f : E →ₗ.[R] F => f.domain → F :=
  ⟨toFun'⟩

@[simp]
theorem toFun_eq_coe (f : E →ₗ.[R] F) (x : f.domain) : f.toFun x = f x :=
  rfl
#align linear_pmap.to_fun_eq_coe LinearPMap.toFun_eq_coe

def mkSpanSingleton' (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) :
    E →ₗ.[R] F where
  domain := R ∙ x
  toFun :=
    have H : ∀ c₁ c₂ : R, c₁ • x = c₂ • x → c₁ • y = c₂ • y := by
      intro c₁ c₂ h
      rw [← sub_eq_zero, ← sub_smul] at h ⊢
      exact H _ h
    { toFun := fun z => Classical.choose (mem_span_singleton.1 z.prop) • y
      -- Porting note(#12129): additional beta reduction needed

def mkSpanSingleton {K E F : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (x : E) (y : F) (hx : x ≠ 0) : E →ₗ.[K] F :=
  mkSpanSingleton' x y fun c hc =>
    (smul_eq_zero.1 hc).elim (fun hc => by rw [hc, zero_smul]) fun hx' => absurd hx' hx
#align linear_pmap.mk_span_singleton LinearPMap.mkSpanSingleton

def fst (p : Submodule R E) (p' : Submodule R F) : E × F →ₗ.[R] E where
  domain := p.prod p'
  toFun := (LinearMap.fst R E F).comp (p.prod p').subtype
#align linear_pmap.fst LinearPMap.fst

def snd (p : Submodule R E) (p' : Submodule R F) : E × F →ₗ.[R] F where
  domain := p.prod p'
  toFun := (LinearMap.snd R E F).comp (p.prod p').subtype
#align linear_pmap.snd LinearPMap.snd

def eqLocus (f g : E →ₗ.[R] F) : Submodule R E where
  carrier := { x | ∃ (hf : x ∈ f.domain) (hg : x ∈ g.domain), f ⟨x, hf⟩ = g ⟨x, hg⟩ }
  zero_mem' := ⟨zero_mem _, zero_mem _, f.map_zero.trans g.map_zero.symm⟩
  add_mem' := fun {x y} ⟨hfx, hgx, hx⟩ ⟨hfy, hgy, hy⟩ =>
    ⟨add_mem hfx hfy, add_mem hgx hgy, by
      erw [f.map_add ⟨x, hfx⟩ ⟨y, hfy⟩, g.map_add ⟨x, hgx⟩ ⟨y, hgy⟩, hx, hy]⟩
  -- Porting note: `by rintro` is required, or error of a free variable happens.
  smul_mem' := by
    rintro c x ⟨hfx, hgx, hx⟩
    exact
      ⟨smul_mem _ c hfx, smul_mem _ c hgx,
        by erw [f.map_smul c ⟨x, hfx⟩, g.map_smul c ⟨x, hgx⟩, hx]⟩
#align linear_pmap.eq_locus LinearPMap.eqLocus

def sup (f g : E →ₗ.[R] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) : E →ₗ.[R] F :=
  ⟨_, Classical.choose (sup_aux f g h)⟩
#align linear_pmap.sup LinearPMap.sup

def supSpanSingleton (f : E →ₗ.[K] F) (x : E) (y : F) (hx : x ∉ f.domain) :
    E →ₗ.[K] F :=
  -- Porting note: `simpa [..]` → `simp [..]; exact ..`
  f.sup (mkSpanSingleton x y fun h₀ => hx <| h₀.symm ▸ f.domain.zero_mem) <|
    sup_h_of_disjoint _ _ <| by simp [disjoint_span_singleton]; exact fun h => False.elim <| hx h
#align linear_pmap.sup_span_singleton LinearPMap.supSpanSingleton

def sSup (c : Set (E →ₗ.[R] F)) (hc : DirectedOn (· ≤ ·) c) : E →ₗ.[R] F :=
  ⟨_, Classical.choose <| sSup_aux c hc⟩
#align linear_pmap.Sup LinearPMap.sSup

def toPMap (f : E →ₗ[R] F) (p : Submodule R E) : E →ₗ.[R] F :=
  ⟨p, f.comp p.subtype⟩
#align linear_map.to_pmap LinearMap.toPMap

def compPMap (g : F →ₗ[R] G) (f : E →ₗ.[R] F) : E →ₗ.[R] G where
  domain := f.domain
  toFun := g.comp f.toFun
#align linear_map.comp_pmap LinearMap.compPMap

def codRestrict (f : E →ₗ.[R] F) (p : Submodule R F) (H : ∀ x, f x ∈ p) : E →ₗ.[R] p
    where
  domain := f.domain
  toFun := f.toFun.codRestrict p H
#align linear_pmap.cod_restrict LinearPMap.codRestrict

def comp (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) (H : ∀ x : f.domain, f x ∈ g.domain) : E →ₗ.[R] G :=
  g.toFun.compPMap <| f.codRestrict _ H
#align linear_pmap.comp LinearPMap.comp

def coprod (f : E →ₗ.[R] G) (g : F →ₗ.[R] G) : E × F →ₗ.[R] G where
  domain := f.domain.prod g.domain
  toFun :=
    -- Porting note: This is just
    -- `(f.comp (LinearPMap.fst f.domain g.domain) fun x => x.2.1).toFun +`
    -- `  (g.comp (LinearPMap.snd f.domain g.domain) fun x => x.2.2).toFun`,
    HAdd.hAdd
      (α := f.domain.prod g.domain →ₗ[R] G)
      (β := f.domain.prod g.domain →ₗ[R] G)
      (f.comp (LinearPMap.fst f.domain g.domain) fun x => x.2.1).toFun
      (g.comp (LinearPMap.snd f.domain g.domain) fun x => x.2.2).toFun
#align linear_pmap.coprod LinearPMap.coprod

def domRestrict (f : E →ₗ.[R] F) (S : Submodule R E) : E →ₗ.[R] F :=
  ⟨S ⊓ f.domain, f.toFun.comp (Submodule.inclusion (by simp))⟩
#align linear_pmap.dom_restrict LinearPMap.domRestrict

def graph (f : E →ₗ.[R] F) : Submodule R (E × F) :=
  f.toFun.graph.map (f.domain.subtype.prodMap (LinearMap.id : F →ₗ[R] F))
#align linear_pmap.graph LinearPMap.graph

def valFromGraph {g : Submodule R (E × F)}
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a ∈ g.map (LinearMap.fst R E F)) : F :=
  (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose
#align submodule.val_from_graph Submodule.valFromGraph

def toLinearPMapAux (g : Submodule R (E × F))
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) :
    g.map (LinearMap.fst R E F) →ₗ[R] F where
  toFun := fun x => valFromGraph hg x.2
  map_add' := fun v w => by
    have hadd := (g.map (LinearMap.fst R E F)).add_mem v.2 w.2
    have hvw := valFromGraph_mem hg hadd
    have hvw' := g.add_mem (valFromGraph_mem hg v.2) (valFromGraph_mem hg w.2)
    rw [Prod.mk_add_mk] at hvw'
    exact (existsUnique_from_graph @hg hadd).unique hvw hvw'
  map_smul' := fun a v => by
    have hsmul := (g.map (LinearMap.fst R E F)).smul_mem a v.2
    have hav := valFromGraph_mem hg hsmul
    have hav' := g.smul_mem a (valFromGraph_mem hg v.2)
    rw [Prod.smul_mk] at hav'
    exact (existsUnique_from_graph @hg hsmul).unique hav hav'

open scoped Classical in
/-- Define a `LinearPMap` from its graph.

In the case that the submodule is not a graph of a `LinearPMap` then the underlying linear map
is just the zero map. -/
noncomputable def toLinearPMap (g : Submodule R (E × F)) : E →ₗ.[R] F
    where
  domain := g.map (LinearMap.fst R E F)
  toFun := if hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0 then
    g.toLinearPMapAux hg else 0
#align submodule.to_linear_pmap Submodule.toLinearPMap

structure LinearPMap (R : Type u) [Ring R] (E : Type v) [AddCommGroup E] [Module R E] (F : Type w)
  [AddCommGroup F] [Module R F] where
  domain : Submodule R E
  toFun : domain →ₗ[R] F
#align linear_pmap LinearPMap