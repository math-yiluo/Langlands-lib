/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothRelativeDimensionCover
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomUnitTensorComparison
public import WeilConjectures.EtaleCohomology.TateTwist.FiniteEndomorphisms
public import WeilConjectures.Mathlib.Topology.NoetherianSpace
public import WeilConjectures.PoincareDuality.Biduality.CoefficientChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCoverIsIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralDualizable
public import WeilConjectures.SmoothPurity.IntegralDualizingComplexIso
public import WeilConjectures.SmoothPurity.TateTwistPullback

/-!
# The relative dualizing complex of a smooth morphism is dualizable

For a smooth morphism `f : X ⟶ Y` of separated `k`-schemes of finite type, the relative dualizing
complex `ω_f = Rf^! ℚ̄_ℓ` is a dualizable object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`
(`ProEtale.CondensedRing.isDualizable_upperShriek_unit_of_smooth`).

Dualizability is local on `X` for open covers, so we may assume `X` connected and `f` of pure
relative dimension `d`. Then `ω_f` is the extension of scalars along `𝒪_E ⟶ ℚ̄_ℓ` of the integral
relative dualizing complex `Rf^! 𝒪_E`
(`ProEtale.CondensedRing.integersToPadicAlgClUpperShriekUnitIso`,
the coefficient comparison for `f^!`), which is isomorphic to the dualizable shifted integral Tate
twist `𝒪_E(d)[2d]` (`ProEtale.CondensedRing.nonempty_iso_integralTateTwist_upperShriekUnit`, whose
finiteness hypothesis holds on a connected scheme by
`AlgebraicGeometry.Etale.finite_endomorphisms_tateObject`); extension of scalars is monoidal.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The extension of scalars along `𝒪_E ⟶ E ⟶ ℚ̄_ℓ` of the integral relative dualizing complex is
the relative dualizing complex: `T_X (Rf^! 𝒪_E) ≅ Rf^! ℚ̄_ℓ`, the coefficient comparisons for `f^!`
(`boundedConstructibleUpperShriekExtendScalarsIso`,
`isIso_boundedConstructibleUpperShriekToPadicAlgCl`)
at the unit, followed by the unit comparisons of the monoidal functors `T`. -/
noncomputable def integersToPadicAlgClUpperShriekUnitIso (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (f : X ⟶ Y) :
    (boundedConstructibleExtendScalars X.left ℓ E ⋙ constructibleToPadicAlgCl X.left ℓ E).obj
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f).obj (𝟙_ _)) ≅
      (boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _) :=
  haveI := isIso_boundedConstructibleUpperShriekToPadicAlgCl ℓ E f
  (constructibleToPadicAlgCl X.left ℓ E).mapIso
      ((boundedConstructibleUpperShriekExtendScalarsIso ℓ E f).app (𝟙_ _) ≪≫
        (ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f).mapIso
          (Functor.Monoidal.εIso (boundedConstructibleExtendScalars _ ℓ E)).symm) ≪≫
    asIso ((boundedConstructibleUpperShriekToPadicAlgCl ℓ E f).app (𝟙_ _)) ≪≫
    (boundedConstructibleUpperShriek ℓ f).mapIso
      (Functor.Monoidal.εIso (constructibleToPadicAlgCl _ ℓ E)).symm

/-- **The relative dualizing complex of a morphism smooth of pure relative dimension with connected
source is dualizable.** -/
theorem isDualizable_upperShriek_unit_of_connectedSpace (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left] [ConnectedSpace X.left] :
    IsDualizable ((boundedConstructibleUpperShriek ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) := by
  have := neZero_natCast_of_ringChar_ne ℓ (k := k)
  obtain ⟨e⟩ := nonempty_iso_integralTateTwist_upperShriekUnit (ℓ := ℓ) (E := E.1) f d
  have h₁ := IsDualizable.map (F := boundedConstructibleExtendScalars X.left ℓ E)
    (isDualizable_shift_integralTateTwistBoundedConstructible ℓ E.1 X d (2 * d))
  have h₂ := IsDualizable.map (F := constructibleToPadicAlgCl X.left ℓ E) h₁
  exact (h₂.of_iso ((boundedConstructibleExtendScalars X.left ℓ E ⋙
    constructibleToPadicAlgCl X.left ℓ E).mapIso e)).of_iso
      (integersToPadicAlgClUpperShriekUnitIso ℓ E f)

/-- An object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` whose restrictions to the members of a finite open cover are
dualizable is dualizable. -/
theorem isDualizable_of_forall_isDualizable_upperStar_overRestrictι {ι : Type} [Finite ι]
    (U : ι → X.left.Opens) (hU : (⨆ i, U i) = ⊤) (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : ∀ i, IsDualizable ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (overRestrictι X (U i))).obj L)) :
    IsDualizable L :=
  isDualizable_of_isIso_ihomUnitTensorToIhom ℓ _ (isIso_of_isIso_upperStar_overRestrictι ℓ U hU _
    fun i ↦ isIso_map_ihomUnitTensorToIhom_of_isDualizable ℓ (overRestrictι X (U i)) _ (h i))

/-- **The relative dualizing complex of a morphism smooth of pure relative dimension is
dualizable**: on each connected component of `X` it is
(`isDualizable_upperShriek_unit_of_connectedSpace`). -/
theorem isDualizable_upperShriek_unit_of_smoothOfRelativeDimension (f : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d f.left] :
    IsDualizable ((boundedConstructibleUpperShriek ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  obtain ⟨m, ⟨eqv⟩⟩ := Finite.exists_equiv_fin (_root_.ConnectedComponents X.left)
  have hopen (c : _root_.ConnectedComponents X.left) :
      IsOpen (_root_.ConnectedComponents.mk ⁻¹' {c} : Set X.left) := by
    obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact TopologicalSpace.NoetherianSpace.isOpen_connectedComponent x
  let U (i : Fin m) : X.left.Opens := ⟨_root_.ConnectedComponents.mk ⁻¹' {eqv.symm i}, hopen _⟩
  have hU : (⨆ i, U i) = ⊤ := eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2
    ⟨eqv (_root_.ConnectedComponents.mk x), by simp [U]⟩
  refine isDualizable_of_forall_isDualizable_upperStar_overRestrictι ℓ U hU _ fun c ↦ ?_
  have : ConnectedSpace (overRestrict X (U c)).left := by
    obtain ⟨x, hx⟩ := _root_.ConnectedComponents.surjective_coe (eqv.symm c)
    have hc : ((U c : X.left.Opens) : Set X.left) = connectedComponent x := by
      simp only [U, TopologicalSpace.Opens.coe_mk, ← hx, connectedComponents_preimage_singleton]
    exact isConnected_iff_connectedSpace.1 (hc ▸ isConnected_connectedComponent)
  have : SmoothOfRelativeDimension d (overRestrictι X (U c) ≫ f).left := by
    have := smoothOfRelativeDimension_comp (n := 0) (m := d) (U c).ι f.left
    rw [zero_add] at this
    exact this
  exact (isDualizable_upperShriek_unit_of_connectedSpace ℓ ⟨⊥, inferInstance⟩
    (overRestrictι X (U c) ≫ f) d).of_iso
    ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ (overRestrictι X (U c)) f).app _ ≪≫
      (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ (overRestrictι X (U c))).app _)

/-- **The relative dualizing complex of a smooth morphism is dualizable** (blueprint
`proposition-relative-dualizing-complex`, `proposition-exceptional-inverse-image-smooth-morphism`:
"`ω_f` is pro-étale locally isomorphic to `Λ_X(d)[2d]`"): on the open and closed subschemes where
`f` has pure relative dimension it is
(`isDualizable_upperShriek_unit_of_smoothOfRelativeDimension`). -/
theorem isDualizable_upperShriek_unit_of_smooth (f : X ⟶ Y) [Smooth f.left] :
    IsDualizable ((boundedConstructibleUpperShriek ℓ f).obj
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))) := by
  obtain ⟨ι, _, U, hU, hd⟩ := exists_finite_openCover_smoothOfRelativeDimension f
  refine isDualizable_of_forall_isDualizable_upperStar_overRestrictι ℓ U hU _ fun i ↦ ?_
  obtain ⟨d, hd⟩ := hd i
  exact (isDualizable_upperShriek_unit_of_smoothOfRelativeDimension ℓ
    (overRestrictι X (U i) ≫ f) d).of_iso
      ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ (overRestrictι X (U i)) f).app _ ≪≫
        (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ (overRestrictι X (U i))).app _)

end AlgebraicGeometry.ProEtale.CondensedRing
