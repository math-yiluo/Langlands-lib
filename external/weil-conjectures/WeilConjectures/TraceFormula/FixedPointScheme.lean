/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.FrobeniusFixedLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.SpreadingOut
public import WeilConjectures.TraceFormula.FixedPoint

/-!

# The fixed scheme of a Frobenius

For a finite type `σ`, the disjoint union `∐_σ Spec k` of copies of the base point is a scheme
finite over `Spec k` (`ProEtale.CondensedRing.sigmaPoint`), whose components are open and
closed points (`ProEtale.CondensedRing.sigmaPointι`).

For the model Frobenius `Φ` of `X = X₀ ×_{k₀} k`, the rational points fixed by the iterate `Φ_m`
induce a morphism `∐_{x ∈ X(k)^{Φ_m}} Spec k ⟶ X` equalizing `𝟙` and `Φ_m`
(`ProEtale.CondensedRing.fixedPointsι`).

## Main statements

- `ProEtale.CondensedRing.IsModelFrobenius.nonempty_isLimit_fixedPointsFork`: this
  morphism is an equalizer of `𝟙` and `Φ_m`, i.e. the fixed scheme `Fix(Φ_m)` is the disjoint
  union of copies of `Spec k` indexed by the fixed rational points (blueprint
  `lemma-frobenius-fixed-scheme--1`). A morphism `g : T ⟶ X` fixed by `Φ_m` is constant near
  every point of `T` (`ProEtale.CondensedRing.IsModelFrobenius.exists_opens_comp_eq`), so `T`
  is the disjoint union of the open pieces `g⁻¹(x)`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k]

/-! ### Disjoint unions of points -/

section SigmaPoint

variable (k) (σ : Type u)

/-- The disjoint union `∐_σ Spec k` of copies of the base point, over `Spec k`. -/
noncomputable def sigmaPoint : Over (Spec (.of k)) :=
  Over.mk (Sigma.desc fun _ : σ ↦ 𝟙 (Spec (.of k)))

/-- The structure morphism of `∐_σ Spec k` is `∐_σ Spec k ≅ Spec (σ → k) ⟶ Spec k`. -/
lemma sigmaDesc_id_eq_sigmaSpec_comp :
    (Sigma.desc fun _ : σ ↦ 𝟙 (Spec (.of k))) =
      sigmaSpec (fun _ : σ ↦ CommRingCat.of k) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (σ → k))) := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [Sigma.ι_comp_desc, ι_sigmaSpec_assoc, ← Spec.map_comp, ← Spec.map_id]
  rfl

/-- The inclusion of a component of `∐_σ Spec k` is `Spec k ⟶ Spec (σ → k) ≅ ∐_σ Spec k`. -/
lemma sigmaι_eq_specMap_comp [Finite σ] (i : σ) :
    Sigma.ι (fun _ : σ ↦ Spec (.of k)) i =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : σ ↦ k) i)) ≫
        inv (sigmaSpec fun _ : σ ↦ CommRingCat.of k) :=
  (IsIso.eq_comp_inv _).2 (ι_sigmaSpec _ i)

instance [Finite σ] : IsFinite (sigmaPoint k σ).hom := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (σ → k)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have h : (sigmaPoint k σ).hom = sigmaSpec (fun _ : σ ↦ CommRingCat.of k) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (σ → k))) :=
    sigmaDesc_id_eq_sigmaSpec_comp k σ
  rw [h]
  infer_instance

/-- The inclusion of the component `i` of `∐_σ Spec k`. -/
noncomputable def sigmaPointι (i : σ) : point k ⟶ sigmaPoint k σ :=
  Over.homMk (Sigma.ι (fun _ : σ ↦ Spec (.of k)) i) (by simp [sigmaPoint])

@[simp]
lemma sigmaPointι_left (i : σ) :
    (sigmaPointι k σ i).left = Sigma.ι (fun _ : σ ↦ Spec (.of k)) i :=
  rfl

instance [Finite σ] (i : σ) : IsOpenImmersion (sigmaPointι k σ i).left := by
  rw [sigmaPointι_left, sigmaι_eq_specMap_comp]
  infer_instance

instance [Finite σ] (i : σ) : IsClosedImmersion (sigmaPointι k σ i).left := by
  rw [sigmaPointι_left, sigmaι_eq_specMap_comp]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : σ ↦ k) i))) :=
    IsClosedImmersion.spec_of_surjective _ (Function.surjective_eval i)
  infer_instance

/-- The components of `∐_σ Spec k` are pairwise disjoint. -/
lemma disjoint_range_sigmaPointι {i i' : σ} (h : i ≠ i') :
    Disjoint (Set.range (sigmaPointι k σ i).left.base)
      (Set.range (sigmaPointι k σ i').left.base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  exact h (congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : σ ↦ Spec (.of k)) i' i b a).mp hb)).symm

/-- The components of `∐_σ Spec k` cover it. -/
lemma iUnion_range_sigmaPointι :
    ⋃ i, Set.range (sigmaPointι k σ i).left.base = Set.univ := by
  refine Set.eq_univ_of_forall fun p ↦ ?_
  obtain ⟨⟨i, a⟩, rfl⟩ := (sigmaMk (fun _ : σ ↦ Spec (.of k))).surjective p
  exact Set.mem_iUnion.mpr ⟨i, a, (sigmaMk_mk (fun _ : σ ↦ Spec (.of k)) i a).symm⟩

end SigmaPoint

/-! ### The fixed points of a Frobenius -/

section FixedPoints

variable {X : Over (Spec (.of k))} (Φ : X ⟶ X) (m : ℕ)

/-- The morphism `∐_{x ∈ X(k)^{Φ_m}} Spec k ⟶ X` given by the rational points fixed by `Φ_m`. -/
noncomputable def fixedPointsι : sigmaPoint k (FixedPoint Φ m) ⟶ X :=
  Over.homMk (Sigma.desc fun x ↦ x.1.left) (by
    refine Sigma.hom_ext _ _ fun x ↦ ?_
    simp [sigmaPoint])

@[reassoc (attr := simp)]
lemma sigmaPointι_fixedPointsι (x : FixedPoint Φ m) :
    sigmaPointι k (FixedPoint Φ m) x ≫ fixedPointsι Φ m = x.1 := by
  ext1
  simp [fixedPointsι, sigmaPointι_left]

/-- The fixed rational points are equalized by `𝟙` and `Φ_m`. -/
lemma fixedPointsι_comp :
    fixedPointsι Φ m ≫ 𝟙 X = fixedPointsι Φ m ≫ frobeniusIterate Φ m := by
  ext1
  refine Sigma.hom_ext _ _ fun x ↦ ?_
  have hx := congrArg Over.Hom.left x.2
  rw [Over.comp_left] at hx
  simp [fixedPointsι, hx]

end FixedPoints

section FixedPointsLimit

variable {X : Over (Spec (.of k))} [IsAlgClosed k] [LocallyOfFiniteType X.hom] {k₀ : Type u}
  [Field k₀] [Finite k₀]
  [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} {Φ : X ⟶ X}
  {m : ℕ}

omit [LocallyOfFiniteType X.hom] in
/-- A point of `X` with values in a local ring and fixed by `Φ_m` factors through a rational
point fixed by `Φ_m` (blueprint `lemma-frobenius-fixed-scheme--1`: the fixed scheme is
reduced). -/
lemma IsModelFrobenius.exists_eq_comp_of_comp_eq_self (hΦ : IsModelFrobenius Φ f₀ p)
    (hm : 1 ≤ m) {A : CommRingCat.{u}} [IsLocalRing A] (t : Spec A ⟶ X.left)
    (ht : t ≫ (frobeniusIterate Φ m).left = t) :
    ∃ x : FixedPoint Φ m, t = t ≫ X.hom ≫ x.1.left := by
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  obtain ⟨x, hxa, hxh, htx⟩ := exists_eq_comp_of_comp_eq_self_of_isFrobenius hΦ.isPullback hm
    (hF₀.pow f₀ m) (Over.w (frobeniusIterate Φ m))
    (IsModelFrobenius.frobeniusIterate_left_comp hp m) t ht
  exact ⟨⟨Over.homMk x hxa, Over.OverMorphism.ext (by simpa using hxh)⟩, htx⟩

/-- A morphism `g : T ⟶ X` fixed by `Φ_m` is, near every point of `T`, the constant map to a
rational point fixed by `Φ_m`. -/
lemma IsModelFrobenius.exists_opens_comp_eq (hΦ : IsModelFrobenius Φ f₀ p) (hm : 1 ≤ m)
    {T : Over (Spec (.of k))} (g : T ⟶ X) (hg : g ≫ frobeniusIterate Φ m = g) (t : T.left) :
    ∃ x : FixedPoint Φ m, ∃ U : T.left.Opens, t ∈ U ∧
      U.ι ≫ g.left = U.ι ≫ T.hom ≫ x.1.left := by
  obtain ⟨x, hx⟩ := hΦ.exists_eq_comp_of_comp_eq_self hm (T.left.fromSpecStalk t ≫ g.left)
    (by rw [Category.assoc, ← Over.comp_left, hg])
  obtain ⟨U, htU, hU⟩ := spread_out_unique_of_locallyOfFiniteType T.hom X.hom g.left
    (T.hom ≫ x.1.left) (Over.w g)
    (by rw [Category.assoc, rationalPoint_left_comp_hom]; exact Category.comp_id _)
    (x := t) (by rw [hx, Category.assoc, ← Category.assoc g.left, Over.w g])
  exact ⟨x, U, htU, hU⟩

/-- Rational points of `X` are determined by their underlying point. -/
lemma rationalPoint_ext {x x' : RationalPoint X}
    (h : x.left (IsLocalRing.closedPoint k) = x'.left (IsLocalRing.closedPoint k)) : x = x' :=
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq X.hom (rationalPoint_left_comp_hom x)
    (rationalPoint_left_comp_hom x') h)

omit [IsAlgClosed k] [LocallyOfFiniteType X.hom] in
/-- A morphism `U ⟶ X` which is the constant map to a rational point `x` sends every point to
the point underlying `x`. -/
lemma comp_rationalPoint_apply {U : Scheme.{u}} (s : U ⟶ Spec (.of k)) (x : RationalPoint X)
    (u : U) : (s ≫ x.left) u = x.left (IsLocalRing.closedPoint k) := by
  rw [Scheme.Hom.comp_apply]
  congr 1
  exact Subsingleton.elim _ _

set_option linter.overlappingInstances false in
/-- **The fixed scheme of a Frobenius** (blueprint `lemma-frobenius-fixed-scheme--1`, a node of
the six-functor chapter): for the model Frobenius `Φ` of `X = X₀ ×_{k₀} k` and `m ≥ 1`, the
fixed scheme `Fix(Φ_m)`, the equalizer of `𝟙` and `Φ_m`, is the disjoint union
`∐ Spec k` of copies of the base point, one for each rational point fixed by `Φ_m` (these
correspond to the `𝔽_{q^m}`-points of `X₀`, `IsModelFrobenius.fixedPointEquiv`).

A morphism `g : T ⟶ X` fixed by `Φ_m` is locally on `T` constant with value a fixed rational
point (`IsModelFrobenius.exists_opens_comp_eq`), so `T` is the disjoint union of the open
pieces `V_x = g⁻¹(x)` and `g` factors uniquely through `∐ Spec k`. -/
theorem IsModelFrobenius.nonempty_isLimit_fixedPointsFork (hΦ : IsModelFrobenius Φ f₀ p)
    (hm : 1 ≤ m) :
    Nonempty (IsLimit (Fork.ofι (fixedPointsι Φ m) (fixedPointsι_comp Φ m))) := by
  classical
  refine ⟨Fork.IsLimit.mk' _ fun s ↦ ?_⟩
  let T := s.pt
  let g : T ⟶ X := s.ι
  have hg : g ≫ frobeniusIterate Φ m = g := by simpa using s.condition.symm
  let pt := IsLocalRing.closedPoint k
  have hloc := hΦ.exists_opens_comp_eq hm g hg
  have hval {x : FixedPoint Φ m} {U : T.left.Opens}
      (hU : U.ι ≫ g.left = U.ι ≫ T.hom ≫ x.1.left) {u : T.left} (hu : u ∈ U) :
      g.left u = x.1.left pt := by
    have h₁ := congr($hU ⟨u, hu⟩)
    rw [← Category.assoc, comp_rationalPoint_apply, Scheme.Hom.comp_apply] at h₁
    simpa using h₁
  -- the open pieces `V_x = g⁻¹(x)`
  let V : FixedPoint Φ m → T.left.Opens := fun x ↦ ⟨{t | g.left t = x.1.left pt}, by
    refine isOpen_iff_forall_mem_open.mpr fun t ht ↦ ?_
    obtain ⟨x', U, htU, hU⟩ := hloc t
    obtain rfl : x' = x := Subtype.ext (rationalPoint_ext ((hval hU htU).symm.trans ht))
    exact ⟨U, fun u hu ↦ hval hU hu, U.isOpen, htU⟩⟩
  have hV (x : FixedPoint Φ m) : (V x).ι ≫ g.left = (V x).ι ≫ T.hom ≫ x.1.left := by
    refine hom_ext_of_forall _ _ fun u ↦ ?_
    obtain ⟨x', U, hu, hU⟩ := hloc ((V x).ι u)
    have hux : g.left ((V x).ι u) = x.1.left pt := by rw [Scheme.Opens.ι_apply]; exact u.2
    obtain rfl : x' = x := Subtype.ext (rationalPoint_ext ((hval hU hu).symm.trans hux))
    refine ⟨(V x').ι ⁻¹ᵁ U, hu, ?_⟩
    have e := Scheme.Hom.resLE_comp_ι (V x').ι (le_refl ((V x').ι ⁻¹ᵁ U))
    rw [← reassoc_of% e, ← reassoc_of% e, hU]
  have hcov : ⨆ x, ((V x).ι).opensRange = ⊤ := by
    simp only [Scheme.Opens.opensRange_ι]
    refine eq_top_iff.mpr fun t _ ↦ ?_
    obtain ⟨x, U, htU, hU⟩ := hloc t
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hval hU htU⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun x ↦ ((V x).ι).opensRange) := by
    intro x x' hxx'
    simp only [Function.onFun, Scheme.Opens.opensRange_ι]
    rw [disjoint_iff, eq_bot_iff]
    rintro t ⟨ht, ht'⟩
    exact (hxx' (Subtype.ext (rationalPoint_ext (ht.symm.trans ht')))).elim
  let hcolim := (nonempty_isColimit_cofanMk_of (fun x ↦ (V x).ι) hcov hdisj).some
  -- the lift `T ⟶ ∐ Spec k`
  let L : T.left ⟶ (sigmaPoint k (FixedPoint Φ m)).left := Cofan.IsColimit.desc hcolim
    fun x ↦ (V x).ι ≫ T.hom ≫ Sigma.ι (fun _ : FixedPoint Φ m ↦ Spec (.of k)) x
  have hL (x : FixedPoint Φ m) : (V x).ι ≫ L =
      (V x).ι ≫ T.hom ≫ Sigma.ι (fun _ : FixedPoint Φ m ↦ Spec (.of k)) x :=
    Cofan.IsColimit.fac hcolim _ x
  have hLw : L ≫ (sigmaPoint k (FixedPoint Φ m)).hom = T.hom :=
    Cofan.IsColimit.hom_ext hcolim _ _ fun x ↦ by
      change (V x).ι ≫ L ≫ _ = (V x).ι ≫ T.hom
      rw [reassoc_of% hL x]
      simp [sigmaPoint]
  refine ⟨Over.homMk L hLw, ?_, fun {l'} hl' ↦ ?_⟩
  · ext1
    refine Cofan.IsColimit.hom_ext hcolim _ _ fun x ↦ ?_
    change (V x).ι ≫ L ≫ (fixedPointsι Φ m).left = (V x).ι ≫ g.left
    rw [reassoc_of% hL x, hV x]
    simp [fixedPointsι]
  · ext1
    refine Cofan.IsColimit.hom_ext hcolim _ _ fun x ↦ ?_
    let l₀ : T.left ⟶ ∐ fun _ : FixedPoint Φ m ↦ Spec (.of k) := l'.left
    have hl₀ : l₀ ≫ Sigma.desc (fun x : FixedPoint Φ m ↦ x.1.left) = g.left := by
      simpa [l₀, g, fixedPointsι] using congrArg (fun φ ↦ φ.left) hl'
    have hl₀w : l₀ ≫ Sigma.desc (fun _ : FixedPoint Φ m ↦ 𝟙 (Spec (.of k))) = T.hom := Over.w l'
    change (V x).ι ≫ l₀ = (V x).ι ≫ L
    rw [hL x]
    have hrange : Set.range ((V x).ι ≫ l₀) ⊆
        Set.range (Sigma.ι (fun _ : FixedPoint Φ m ↦ Spec (.of k)) x) := by
      rintro _ ⟨u, rfl⟩
      obtain ⟨⟨i, a⟩, ha⟩ :=
        (sigmaMk (fun _ : FixedPoint Φ m ↦ Spec (.of k))).surjective (((V x).ι ≫ l₀) u)
      rw [sigmaMk_mk] at ha
      obtain rfl : i = x := by
        have h₁ : (Sigma.desc fun x : FixedPoint Φ m ↦ x.1.left)
            (Sigma.ι (fun _ : FixedPoint Φ m ↦ Spec (.of k)) i a) = i.1.left a := by
          change (Sigma.ι _ i ≫ Sigma.desc fun x : FixedPoint Φ m ↦ x.1.left) a = _
          rw [Sigma.ι_comp_desc]
        have h₂ : (Sigma.desc fun x : FixedPoint Φ m ↦ x.1.left) (((V x).ι ≫ l₀) u) =
            g.left ((V x).ι u) := by
          change ((V x).ι ≫ l₀ ≫ Sigma.desc fun x : FixedPoint Φ m ↦ x.1.left) u = _
          rw [hl₀]
          rfl
        have hux : g.left ((V x).ι u) = x.1.left pt := by
          rw [Scheme.Opens.ι_apply]
          exact u.2
        have : Subsingleton (point k).left := inferInstanceAs (Subsingleton (Spec (.of k)))
        refine Subtype.ext (rationalPoint_ext ?_)
        rw [← hux, ← h₂, ← ha, h₁]
        exact congrArg _ (Subsingleton.elim _ _)
      exact ⟨a, ha⟩
    have e₁ := IsOpenImmersion.lift_fac (Sigma.ι (fun _ : FixedPoint Φ m ↦ Spec (.of k)) x)
      ((V x).ι ≫ l₀) hrange
    have e₂ : Sigma.ι (fun _ : FixedPoint Φ m ↦ Spec (.of k)) x ≫
        Sigma.desc (fun _ : FixedPoint Φ m ↦ 𝟙 (Spec (.of k))) = 𝟙 _ := Sigma.ι_comp_desc _ _
    have hlx : IsOpenImmersion.lift (Sigma.ι (fun _ : FixedPoint Φ m ↦ Spec (.of k)) x)
        ((V x).ι ≫ l₀) hrange = (V x).ι ≫ T.hom := by
      rw [← Category.comp_id (IsOpenImmersion.lift _ _ hrange), ← e₂, reassoc_of% e₁,
        hl₀w]
    rw [← e₁, hlx, Category.assoc]

end FixedPointsLimit

end AlgebraicGeometry.ProEtale.CondensedRing
