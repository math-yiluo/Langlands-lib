/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantExtension
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroupDense
public import WeilConjectures.Mathlib.FieldTheory.Finite.Extension
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
public import WeilConjectures.WeilSheaf.WeilMonodromyGeneral

/-!
# The Weil group in the arithmetic fundamental group

Let `X₀` be a scheme over a finite field `K`, `π : X ⟶ X₀` the projection of its geometric fibre
and `B = (t, β)` base point data (`AlgebraicGeometry.FrobeniusBasePoint`). The Weil group
`π₁(X, t) ⋊ ℤ` of `B` maps to the arithmetic fundamental group `π₁(X₀, t ≫ π)`: a loop `g` at `t`
goes to its image `π_* g`, and the generator of `ℤ` to the *arithmetic Frobenius*
`F₀ = π_* β`, a loop at `t ≫ π` since `Fr ≫ π = π`
(`AlgebraicGeometry.FrobeniusBasePoint.arithMap`).

For `X₀` geometrically connected, quasi-compact and quasi-separated, and `t` a `K̄`-rational
point, this map is injective on `π₁(X, t)`, its image is dense, and the topology of
`π₁(X₀, t ≫ π)` induces on the Weil group the topology of its normal subgroups of finite index
which are open on `π₁(X, t)` (`AlgebraicGeometry.FrobeniusBasePoint.exists_mem_nhds_arithMap`):
this is what is needed to extend bounded representations of the Weil group to `π₁(X₀)`
(Deligne, Weil II, 1.3.14).
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory Topology

namespace AlgebraicGeometry.FrobeniusBasePoint

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  (B : FrobeniusBasePoint K X)

/-- The geometric Galois Frobenius lies over `X₀`, at the base point. -/
lemma frob_comp_geometricFiberProj :
    (B.t ≫ (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom) ≫
      (X ↘ Spec (.of K)).geometricFiberProj = B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj := by
  rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj]

/-- The *arithmetic Frobenius* `F₀ ∈ π₁(X₀, t ≫ π)`: the image `π_* β` of the path
`β : F_t ≅ F_{t ≫ Fr}`, a loop at `t ≫ π` since `Fr ≫ π = π`. -/
noncomputable def arithFrob : Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) :=
  .of (pullbackPathIso (X ↘ Spec (.of K)).geometricFiberProj B.frobPath ≪≫
    eqToIso (congrArg fiber B.frob_comp_geometricFiberProj))

/-- The image of the Frobenius transport of a loop `g` at `t` in `π₁(X₀, t ≫ π)` is the
conjugate `F₀⁻¹ π_*(g) F₀`. -/
lemma pullbackPathHom_frobConj (g : Aut (fiber B.t)) :
    pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t (B.frobConj g) =
      B.arithFrob⁻¹ * pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t g *
        B.arithFrob := by
  apply Aut.ext
  have h := pullbackPathIso_comp (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom
    (X ↘ Spec (.of K)).geometricFiberProj g.asIso
  rw [pullbackPathIso_congr
    (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)] at h
  simp only [pullbackPathHom_apply, frobConj_apply, Aut.mul_asIso, Aut.inv_asIso, arithFrob,
    pullbackPathIso_trans, pullbackPathIso_symm]
  ext1
  have h' := congrArg Iso.hom h
  simp only [Iso.trans_hom, eqToIso.hom] at h'
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Iso.trans_inv, eqToIso.inv,
    Category.assoc]
  rw [← cancel_epi (eqToHom (congrArg fiber (Category.assoc B.t
      (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom
        (X ↘ Spec (.of K)).geometricFiberProj))),
    ← cancel_mono (eqToHom (congrArg fiber (Category.assoc B.t
      (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom
        (X ↘ Spec (.of K)).geometricFiberProj)).symm)] at h'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h'
  rw [← h']
  simp

/-- The inverse Frobenius transport of loops corresponds to conjugation by `F₀`. -/
lemma pullbackPathHom_frobConj_symm (g : Aut (fiber B.t)) :
    pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t (B.frobConj.symm g) =
      B.arithFrob * pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t g *
        B.arithFrob⁻¹ := by
  have h := B.pullbackPathHom_frobConj (B.frobConj.symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  group

/-- The action of `n ∈ ℤ` on `π₁(X, t)` defining the Weil group is conjugation by `F₀ⁿ` in
`π₁(X₀, t ≫ π)`. -/
lemma pullbackPathHom_frobAction (n : ℤ) (g : Aut (fiber B.t)) :
    pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t
        (B.frobAction (Multiplicative.ofAdd n) g) =
      B.arithFrob ^ n * pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t g *
        (B.arithFrob ^ n)⁻¹ := by
  simp only [frobAction, zpowersHom_apply, toAdd_ofAdd]
  induction n using Int.induction_on generalizing g with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, MulAut.mul_apply, ih, MulAut.inv_apply, pullbackPathHom_frobConj_symm]
    group
  | pred n ih =>
    rw [zpow_sub_one, MulAut.mul_apply, ih, inv_inv, pullbackPathHom_frobConj]
    group

/-- **The Weil group in the arithmetic fundamental group**: the homomorphism
`π₁(X, t) ⋊ ℤ → π₁(X₀, t ≫ π)`, `(g, n) ↦ π_*(g) F₀ⁿ`. -/
noncomputable def arithMap :
    B.WeilGroup →* Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) :=
  SemidirectProduct.lift (pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t)
    (zpowersHom _ B.arithFrob) fun n ↦ by
      ext1 g
      have h := B.pullbackPathHom_frobAction (Multiplicative.toAdd n) g
      rw [ofAdd_toAdd] at h
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        zpowersHom_apply]
      exact h

@[simp]
lemma arithMap_inl (g : Aut (fiber B.t)) :
    B.arithMap (SemidirectProduct.inl g) =
      pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t g :=
  SemidirectProduct.lift_inl _ _ _ g

@[simp]
lemma arithMap_inr (n : Multiplicative ℤ) :
    B.arithMap (SemidirectProduct.inr n) = B.arithFrob ^ n.toAdd :=
  SemidirectProduct.lift_inr _ _ _ n

section ConstantCover

variable {B}

/-- The induced path `f_* σ` acts on a point `(x, y)` of the base change as `σ` does. -/
lemma _root_.AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathIso_hom_app_pullbackFiberIso
    {X' Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (f : X' ⟶ Y)
    {y z : Spec (.of Ω) ⟶ X'} (σ : fiber y ≅ fiber z) (P : Y.FiniteEtale)
    (x : (fiber y).obj ((pullback f).obj P)) :
    (pullbackPathIso f σ).hom.app P ((pullbackFiberIso f y).hom.app P x) =
      (pullbackFiberIso f z).hom.app P (σ.hom.app _ x) := by
  simp only [pullbackPathIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, FintypeCat.comp_apply]
  congr 2
  exact ConcreteCategory.congr_hom ((pullbackFiberIso f y).hom_inv_id_app P) x

/-- The loops at a `K̄`-rational point `t` of the geometric fibre act trivially, through
`π₁(X, t) → π₁(X₀, t ≫ π)`, on the geometric fibres of the constant covers. -/
lemma pullbackPathHom_hom_app_constantCover
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _)
    (g : Aut (fiber B.t)) (A : FiniteEtaleAlgebra K)
    (y : (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).obj
      (constantCover (X ↘ Spec (.of K)) A)) :
    (pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t g).asIso.hom.app _ y = y := by
  obtain ⟨z, rfl⟩ : ∃ z, (pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t).hom.app _ z
      = y := ⟨_, ConcreteCategory.congr_hom
        ((pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t).inv_hom_id_app _) y⟩
  rw [pullbackPathHom_apply, pullbackPathIso_hom_app_pullbackFiberIso]
  congr 1
  obtain ⟨σ, hσ, hz⟩ := exists_section_pullback_constantCover (X ↘ Spec (.of K)) A ht z
  exact fiber_ext _ ((path_section g.asIso _ σ hσ z hz).trans hz.symm)

/-- The geometric Galois Frobenius `Fr` of `X = X₀ ×_K K̄` followed by the section of a
`K̄`-point `u` of `Spec A` and the arithmetic Frobenius of `X₀ ×_K Spec A` is the section of `u`:
on the `Spec A`-component, `Fr` acts by the geometric Frobenius `σ` of `K̄`, which the arithmetic
Frobenius `x ↦ x ^ q` of `A` undoes. -/
lemma geometricGaloisFrobenius_sectionOfPoint_arithmeticFrobenius (A : FiniteEtaleAlgebra K)
    (u : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of A.1))
    (hu : u ≫ A.specHom = (Scheme.specAlgebraicClosure K).hom) :
    (X ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom ≫
        sectionOfPoint (X ↘ Spec (.of K)) A u hu ≫
          Limits.pullback.fst (constantCover (X ↘ Spec (.of K)) A).obj.hom
            (X ↘ Spec (.of K)).geometricFiberProj ≫
            (arithmeticFrobenius (X ↘ Spec (.of K)) A).hom.hom.left =
      sectionOfPoint (X ↘ Spec (.of K)) A u hu ≫
        Limits.pullback.fst (constantCover (X ↘ Spec (.of K)) A).obj.hom
          (X ↘ Spec (.of K)).geometricFiberProj := by
  apply Limits.pullback.hom_ext
  · simp [arithmeticFrobenius, constantCoverIso, -constantCover_obj_hom]
  · simp [arithmeticFrobenius, constantCoverIso, comp_specMap_frobenius, -constantCover_obj_hom]

/-- **The arithmetic Frobenius is a Frobenius**: at a `K̄`-rational base point, `F₀` acts on the
geometric fibres of the constant covers as the geometric Frobenius. -/
lemma arithFrob_hom_app_constantCover
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _)
    (A : FiniteEtaleAlgebra K)
    (y : (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).obj
      (constantCover (X ↘ Spec (.of K)) A)) :
    B.arithFrob.asIso.hom.app _ y =
      geometricFrobenius (X ↘ Spec (.of K)) (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) A y := by
  obtain ⟨z, rfl⟩ : ∃ z, (pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t).hom.app _ z
      = y := ⟨_, ConcreteCategory.congr_hom
        ((pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t).inv_hom_id_app _) y⟩
  have hz := left_eq_sectionOfPoint (X ↘ Spec (.of K)) ht A z
  have hβ := path_section B.frobPath _ _ (sectionOfPoint_snd (X ↘ Spec (.of K)) A _ _) z hz
  have hinj : Function.Injective ((fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).map
      (arithmeticFrobenius (X ↘ Spec (.of K)) A).hom) :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  apply hinj
  rw [fiber_map_arithmeticFrobenius_geometricFrobenius]
  apply fiber_ext
  simp only [arithFrob, Iso.trans_hom, NatTrans.comp_app, FintypeCat.comp_apply, fiber_map_left]
  rw [eqToIso_fiber_hom_app_left (B.frob_comp_geometricFiberProj),
    pullbackPathIso_hom_app_pullbackFiberIso, pullbackFiberIso_hom_app_left,
    pullbackFiberIso_hom_app_left, hβ, hz]
  simp only [Category.assoc]
  rw [geometricGaloisFrobenius_sectionOfPoint_arithmeticFrobenius]

/-- The Weil group acts on the geometric fibres of the constant covers through its degree: the
element `(g, n)` acts as the `n`-th power of the geometric Frobenius. -/
lemma arithMap_hom_app_constantCover
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _)
    (w : B.WeilGroup) (A : FiniteEtaleAlgebra K)
    (y : (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).obj
      (constantCover (X ↘ Spec (.of K)) A)) :
    (B.arithMap w).asIso.hom.app _ y = (geometricFrobenius (X ↘ Spec (.of K))
      (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) A ^ w.right.toAdd) y := by
  set φ := MulAction.toPermHom (Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)))
    ((fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).obj
      (constantCover (X ↘ Spec (.of K)) A))
  have h₁ (g : Aut (fiber B.t)) : φ (B.arithMap (SemidirectProduct.inl g)) = 1 :=
    Equiv.ext fun y ↦ by
      rw [arithMap_inl]
      exact pullbackPathHom_hom_app_constantCover ht g A y
  have h₂ : φ B.arithFrob = geometricFrobenius (X ↘ Spec (.of K))
      (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) A :=
    Equiv.ext fun y ↦ arithFrob_hom_app_constantCover ht A y
  have h : φ (B.arithMap w) = geometricFrobenius (X ↘ Spec (.of K))
      (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) A ^ w.right.toAdd := by
    have hw : B.arithMap w = B.arithMap (SemidirectProduct.inl w.left) *
        B.arithMap (SemidirectProduct.inr w.right) := by
      rw [← map_mul, SemidirectProduct.inl_left_mul_inr_right]
    rw [hw, map_mul, h₁, one_mul, arithMap_inr, map_zpow, h₂]
  exact Equiv.ext_iff.1 h y

end ConstantCover

/-- The action of the Weil group on the geometric fibre of a constant cover, as permutations: the
degree-`n` part acts as the `n`-th power of the geometric Frobenius. -/
lemma toPermHom_arithMap (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _)
    (w : B.WeilGroup) (A : FiniteEtaleAlgebra K) :
    MulAction.toPermHom (Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)))
        ((fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).obj
          (constantCover (X ↘ Spec (.of K)) A)) (B.arithMap w) =
      geometricFrobenius (X ↘ Spec (.of K)) (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) A ^
        w.right.toAdd :=
  Equiv.ext fun y ↦ arithMap_hom_app_constantCover ht w A y

section Small

variable {Y Y' : Scheme.{u}} [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The map `π₁(Y', y) → π₁(Y, y ≫ f)` of automorphism groups of fibre functors is the map of
fundamental groups `AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap` along the path
`F_y ∘ f^* ≅ F_{y ≫ f}`, for any models `G'` and `G` of the fundamental groups. -/
lemma _root_.AlgebraicGeometry.Scheme.FiniteEtale.toAut_fundamentalGroupMap (f : Y' ⟶ Y)
    (y : Spec (.of Ω) ⟶ Y') (G' : Type u) [Group G'] [∀ P, MulAction G' ((fiber y).obj P)]
    [IsNaturalSMul (fiber y) G'] (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [∀ P, MulAction G ((fiber (y ≫ f)).obj P)]
    [IsFundamentalGroup (fiber (y ≫ f)) G] (g : G') :
    toAut (fiber (y ≫ f)) G (fundamentalGroupMap (pullbackFiberIso f y) G' G g) =
      pullbackPathHom f y (toAut (fiber y) G' g) := by
  ext P x
  obtain ⟨z, rfl⟩ : ∃ z, (pullbackFiberIso f y).hom.app P z = x :=
    ⟨_, ConcreteCategory.congr_hom ((pullbackFiberIso f y).inv_hom_id_app P) x⟩
  rw [toAut_hom_app_apply, fundamentalGroupMap_smul, pullbackPathHom_apply,
    pullbackPathIso_hom_app_pullbackFiberIso, toAut_hom_app_apply]

end Small

omit [Finite K] in
/-- The geometric fibre of a geometrically connected scheme is connected. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.connectedSpace_geometricFiber {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of K)) [GeometricallyConnected f] : ConnectedSpace f.geometricFiber :=
  GeometricallyConnected.geometrically_connectedSpace (f := f)
    (Scheme.specAlgebraicClosure K).hom f.geometricFiberProj
    f.geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)

variable [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]

/-- **The homotopy exact sequence, injectivity**: `π₁(X, t) → π₁(X₀, t ≫ π)` is injective. -/
theorem injective_pullbackPathHom [ConnectedSpace (X ↘ Spec (.of K)).geometricFiber] :
    Function.Injective (pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t) := by
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup B.t
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)
  intro a b hab
  obtain ⟨a', rfl⟩ := (toAut_bijective (fiber B.t) G').2 a
  obtain ⟨b', rfl⟩ := (toAut_bijective (fiber B.t) G').2 b
  rw [← toAut_fundamentalGroupMap _ _ G' G, ← toAut_fundamentalGroupMap _ _ G' G] at hab
  rw [fundamentalGroupMap_injective_geometricFiber (X ↘ Spec (.of K))
    (pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t) G' G
    ((toAut_bijective _ G).1 hab)]

/-- **The Weil group is dense in the arithmetic fundamental group**: the image of
`π₁(X, t) ⋊ ℤ → π₁(X₀, t ≫ π)` is dense, for `X₀` geometrically connected and `t` rational. -/
theorem denseRange_arithMap [GeometricallyConnected (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _) :
    DenseRange B.arithMap := by
  have := (X ↘ Spec (.of K)).connectedSpace_geometricFiber
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup B.t
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)
  let e := toAut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) G
  set H := B.arithMap.range.topologicalClosure
  have hHG : H.comap e = ⊤ := by
    refine eq_top_of_forall_mem_weilGroup (X ↘ Spec (.of K))
      (t := B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) G _ ?_ fun w hw ↦ ?_
    · rw [Subgroup.coe_comap]
      exact B.arithMap.range.isClosed_topologicalClosure.preimage (toAut_continuous _ G)
    rw [mem_weilGroup_iff] at hw
    set ρ := e w.1 * (B.arithMap (SemidirectProduct.inr w.2))⁻¹
    have hρ : (toAutMulEquiv _ G).symm ρ ∈ (fundamentalGroupMap
        (pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t) G' G).range := by
      refine mem_range_fundamentalGroupMap_of_mem_weilGroup (X ↘ Spec (.of K)) _ G' G _
        ((mem_weilGroup_iff _ _ _).2 fun A y ↦ ?_)
      have h₁ : MulAction.toPermHom _ _ (e w.1) = geometricFrobenius (X ↘ Spec (.of K))
          (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) A ^ w.2.toAdd :=
        Equiv.ext fun y ↦ (toAut_hom_app_apply _ _ _).trans (hw A y)
      have h₂ := B.toPermHom_arithMap ht (SemidirectProduct.inr w.2) A
      rw [SemidirectProduct.right_inr] at h₂
      have h₃ : MulAction.toPermHom (Aut _)
          ((fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).obj
            (constantCover (X ↘ Spec (.of K)) A)) ρ = 1 := by
        rw [map_mul, map_inv, h₁, h₂, mul_inv_cancel]
      rw [← toAut_hom_app_apply (fiber _) (G := G), ← toAutMulEquiv_apply,
        MulEquiv.apply_symm_apply]
      exact Equiv.ext_iff.1 h₃ y
    obtain ⟨g, hg⟩ := hρ
    have hw' : e w.1 = B.arithMap (SemidirectProduct.inl (toAut (fiber B.t) G' g) *
        SemidirectProduct.inr w.2) := by
      have hsymm : toAut _ G ((toAutMulEquiv _ G).symm ρ) = ρ :=
        (toAutMulEquiv_apply _ _).symm.trans (MulEquiv.apply_symm_apply _ _)
      rw [map_mul, arithMap_inl, ← toAut_fundamentalGroupMap _ _ G' G, hg, hsymm,
        inv_mul_cancel_right]
    exact Subgroup.le_topologicalClosure _ ⟨_, hw'.symm⟩
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro π
  obtain ⟨g, rfl⟩ := (toAut_bijective _ G).2 π
  have hg : g ∈ H.comap e := hHG ▸ Subgroup.mem_top g
  exact hg

/-- For every `M > 0` some point of the geometric fibre of a constant cover is fixed by `Φⁿ` only
if `M ∣ n`: take the constant cover of an extension of degree `M`. -/
lemma _root_.AlgebraicGeometry.Scheme.FiniteEtale.exists_geometricFrobenius_zpow_dvd
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K)) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Y) (M : ℕ) [NeZero M] :
    ∃ (A : FiniteEtaleAlgebra K) (z : (fiber s).obj (constantCover p A)), ∀ n : ℤ,
      (geometricFrobenius p s A ^ n) z = z → (M : ℤ) ∣ n := by
  obtain ⟨L, hLM⟩ := FiniteField.exists_intermediateField_finrank_eq K (AlgebraicClosure K)
    (Nat.pos_of_ne_zero (NeZero.ne M))
  have hL : FiniteDimensional K L :=
    Module.finite_of_finrank_pos (hLM ▸ Nat.pos_of_ne_zero (NeZero.ne M))
  have : Algebra.Etale K L := (FiniteSubfield.toFiniteEtaleAlgebra ⟨L, hL⟩).2.2
  let : Algebra K Ω := (baseRingHom p s).toAlgebra
  let ψ : L →ₐ[K] Ω := IsSepClosed.lift
  refine ⟨FiniteEtaleAlgebra.of L, (fiberConstantCoverEquiv p s (FiniteEtaleAlgebra.of L)).symm
    ⟨ψ.toRingHom, ψ.comp_algebraMap⟩, fun n hn ↦ ?_⟩
  rw [← hLM]
  exact dvd_of_geometricFrobenius_zpow_apply p s L _ n hn

/-- **The topology of `π₁(X₀)` on the Weil group** (cf. Deligne, Weil II, 1.3.14): every normal
subgroup `H` of finite index of the Weil group `π₁(X, t) ⋊ ℤ` which is open on `π₁(X, t)` contains
the preimage of a neighbourhood of `1` of `π₁(X₀, t ≫ π)`. Take an open subgroup `O₁` of
`π₁(X₀)` cutting out `H ∩ π₁(X, t)` (`π₁(X) → π₁(X₀)` is a closed embedding), `m₁ > 0` with
`F₀^{m₁} ∈ O₁`, `m₂ > 0` with `γ^{m₂} ∈ H`, and the stabiliser `O₂` of a point of a constant cover
of degree `m₁ m₂`: if `(g, n)` maps into `O₁ ∩ O₂`, then `m₁ m₂ ∣ n`, so `π_* g ∈ O₁` and
`(g, n) ∈ H`. -/
theorem exists_mem_nhds_arithMap [ConnectedSpace (X ↘ Spec (.of K)).geometricFiber]
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _)
    (H : Subgroup B.WeilGroup) [H.Normal] [H.FiniteIndex]
    (hH : IsOpen (SemidirectProduct.inl ⁻¹' (H : Set B.WeilGroup))) :
    ∃ O ∈ 𝓝 (1 : Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj))),
      ∀ w, B.arithMap w ∈ O → w ∈ H := by
  have hemb := ((continuous_pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj
    B.t).isClosedEmbedding B.injective_pullbackPathHom).isEmbedding
  obtain ⟨O', hO'open, hO'⟩ := hemb.isInducing.isOpen_iff.1 hH
  have h1 : (1 : Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj))) ∈ O' := by
    have h : (1 : Aut (fiber B.t)) ∈ SemidirectProduct.inl ⁻¹' (H : Set B.WeilGroup) := by
      simp only [Set.mem_preimage, map_one, SetLike.mem_coe, H.one_mem]
    rw [← hO'] at h
    simpa using h
  obtain ⟨X₁, -, hX₁⟩ :=
    (nhds_one_has_basis_stabilizers (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj))).mem_iff.1
      (hO'open.mem_nhds h1)
  -- a power of `F₀` lies in the stabiliser `O₁` of `X₁`
  obtain ⟨m₁, hm₁, hFm₁⟩ : ∃ m₁ : ℕ, 0 < m₁ ∧ B.arithFrob ^ m₁ ∈ MulAction.stabilizer _ X₁.pt := by
    set σ := MulAction.toPermHom _ ((fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).obj
      X₁.obj) B.arithFrob with hσ
    refine ⟨orderOf σ, (isOfFinOrder_of_finite σ).orderOf_pos, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    have h := congrArg (fun τ : Equiv.Perm _ ↦ τ X₁.pt) (pow_orderOf_eq_one σ)
    rw [hσ, ← map_pow] at h
    exact h
  -- a power of the generator `γ` of `ℤ` lies in `H`
  obtain ⟨m₂, hm₂, hγ⟩ : ∃ m₂ : ℕ, 0 < m₂ ∧
      (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)) : B.WeilGroup) ^ m₂ ∈ H := by
    have : Finite (B.WeilGroup ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
    let γ : B.WeilGroup ⧸ H := (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)) :
      B.WeilGroup)
    refine ⟨orderOf γ, (isOfFinOrder_of_finite γ).orderOf_pos, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]
  -- a constant cover of degree `m₁ m₂`
  have : NeZero (m₁ * m₂) := ⟨(Nat.mul_pos hm₁ hm₂).ne'⟩
  obtain ⟨A, z, hz⟩ := exists_geometricFrobenius_zpow_dvd (X ↘ Spec (.of K))
    (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) (m₁ * m₂)
  refine ⟨(MulAction.stabilizer (Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj))) X₁.pt :
      Set _) ∩ MulAction.stabilizer (Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj))) z,
    Filter.inter_mem ((stabilizer_isOpen _ _).mem_nhds (Subgroup.one_mem _))
      ((stabilizer_isOpen _ _).mem_nhds (Subgroup.one_mem _)), fun w hw ↦ ?_⟩
  obtain ⟨hw₁, hw₂⟩ := hw
  obtain ⟨k, hk⟩ := hz w.right.toAdd (by
    rw [← B.toPermHom_arithMap ht w A]
    exact hw₂)
  -- the geometric part lies in `H`
  have hdecomp : B.arithMap (SemidirectProduct.inl w.left) =
      B.arithMap w * (B.arithFrob ^ m₁) ^ (-(m₂ * k : ℤ)) := by
    have hw : B.arithMap w = B.arithMap (SemidirectProduct.inl w.left) *
        B.arithFrob ^ w.right.toAdd := by
      rw [← arithMap_inr, ← map_mul, SemidirectProduct.inl_left_mul_inr_right]
    have hexp : ((m₁ * m₂ : ℕ) : ℤ) * k + m₁ * -(m₂ * k) = 0 := by
      push_cast
      ring
    rw [hw, hk, ← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add, hexp, zpow_zero, mul_one]
  have hg : SemidirectProduct.inl w.left ∈ H := by
    have hmem : pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t w.left ∈ O' := by
      rw [← arithMap_inl, hdecomp]
      exact hX₁ (mul_mem hw₁ (zpow_mem hFm₁ _))
    have h := Set.mem_preimage.2 hmem
    rwa [hO'] at h
  have hr : (SemidirectProduct.inr w.right : B.WeilGroup) ∈ H := by
    have h : (SemidirectProduct.inr w.right : B.WeilGroup) =
        ((SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ)) : B.WeilGroup) ^ m₂) ^
          (m₁ * k) := by
      rw [← map_pow, ← map_zpow]
      congr 1
      apply Multiplicative.toAdd.injective
      rw [toAdd_zpow, toAdd_pow, toAdd_ofAdd, hk, smul_eq_mul, nsmul_eq_mul, mul_one]
      push_cast
      ring
    rw [h]
    exact zpow_mem hγ _
  rw [← SemidirectProduct.inl_left_mul_inr_right w]
  exact mul_mem hg hr

end AlgebraicGeometry.FrobeniusBasePoint
