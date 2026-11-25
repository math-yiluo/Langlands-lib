/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionData
import WeilConjectures.Algebra.Homology.PrincipalReduction.Setup.PrincipalReductionComparison
import WeilConjectures.PoincareDuality.Point.PointPrincipalReductionCoefficients
import WeilConjectures.PoincareDuality.Point.PointReductionCoefficientRing
import WeilConjectures.PoincareDuality.ScalarReductionCochainComparison
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Point sections commute with derived principal reduction

The coefficient sequence, flat-resolution comparison and localization descent follow
steps 1--10 of the original proof. No point-reduction normalization theorem is used.
(blueprint: lem-pod-point-sections-derived-reduction-iso) -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

private theorem pointAbSectionsExact (k : Type u) [Field k] [IsAlgClosed k] :
    exactFunctor _ _ ((sheafSections (ProEt.topology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj (op (ProEt.mk (𝟙 (Spec (.of k)))))) := by
  let F := (sheafSections (ProEt.topology (Spec (.of k)))
    AddCommGrpCat.{u + 1}).obj (op (ProEt.mk (𝟙 (Spec (.of k)))))
  have : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf (ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1} ⋙
        (evaluation (Spec (.of k)).ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op (ProEt.mk (𝟙 (Spec (.of k)))))))
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let : F.PreservesEpimorphisms :=
    ⟨fun {X Y} f hf ↦ (AddCommGrpCat.epi_iff_surjective _).2
      ((@point_proEtale_sections_exact.{u, u + 1, u + 1} k _ _).1 X Y f hf)⟩
  let : F.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels F
  exact (exactFunctor_iff _).2
    ⟨inferInstance, Functor.preservesFiniteColimits_of_preservesHomology F⟩

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Exact point sections commute with derived principal reduction.
Source: Stacks Tags 06Y6 and 06YY; original blueprint steps 1--10.
(blueprint: lem-pod-point-sections-derived-reduction-iso) -/
theorem point_sections_derived_reduction_iso (_hl : l ≠ D.p) (n : ℕ) :
    Nonempty (pointReductionTensorSections D l E n ≅ pointReductionSectionsTensor D l E n) := by
  let T := Spec (.of D.k)
  let J := ProEt.topology T
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
  have : IsDomain R := (ULift.ringEquiv : R ≃+* _).toMulEquiv.isDomain _
  have : HasSheafify J AddCommGrpCat.{u + 1} := integralCoefficientAbSheafify.{u, u} T
  have : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, u} T
  have : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let U := ProEt.mk (𝟙 T)
  obtain ⟨hz, hs⟩ := pointPrincipalReductionCoefficients D.k l E n
  let δ : SheafOfModules.PrincipalReduction.Setup (C := T.ProEt) (J := J) R :=
    { U := U
      terminal := MorphismProperty.Over.mkIdTerminal @WeaklyEtale T
      O := completedIntegralCommRingSheafUnrestricted l E T
      S := integralCoefficientCommRingSheaf l E T n
      ρ := pointIntegralSectionMap l E D.k
      t := ULift.up (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)
      φ := completedIntegralCommRingProjectionUnrestricted l E T n
      A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
      quotientMap := pointReductionQuotient l E n
      quotient_surjective := (pointReductionQuotient_properties l E n).2.1
      quotient_kernel := (pointReductionQuotient_properties l E n).2.2
      quotientSectionsMap := pointConstantSectionMap D.k
        (Padic.coefficientExtensionRing l E (n + 1))
      quotient_sections_comm := by
        intro x
        let q := CommRingCat.ofHom (pointReductionQuotient l E n)
        have hn := congrArg (fun h ↦ h.app (op U) x)
          (toSheafify_naturality J ((Functor.const T.ProEtᵒᵖ).map q))
        have hc := congrArg (fun h ↦ h.hom.app (op U)
          ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of R))).app (op U) x))
          (limit.lift_π (integralConstantCoefficientCone l E T) (op n))
        exact hn.trans hc.symm
      zero := hz
      shortExact := hs
      sectionsExact := pointAbSectionsExact D.k }
  have ht : δ.t ≠ 0 := by
    intro h
    have hzero : δ.t * (0 : R) = δ.t * (1 : R) := by rw [h]; simp
    exact zero_ne_one ((pointReductionQuotient_properties l E n).1 hzero)
  obtain ⟨e⟩ := δ.comparison ht
  obtain ⟨j⟩ := scalarReductionCochainModel_iso l E T n δ.extension
  let e' := e ≪≫ Functor.isoWhiskerRight j δ.G'
  exact ⟨Functor.isoWhiskerLeft (sfIntegralConstructible l E T).ι e'⟩

end WeilConjectures
