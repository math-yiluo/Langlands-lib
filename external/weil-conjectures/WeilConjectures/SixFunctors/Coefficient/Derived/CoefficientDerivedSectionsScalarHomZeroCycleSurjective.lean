/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroRepresentativeData
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.SixFunctors.Coefficient.CoefficientHomZeroClass
import all WeilConjectures.SixFunctors.Coefficient.CoefficientHomZeroClass

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open SheafOfModules (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses)
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Every H-zero class has a cycle representative after transporting the target
through a chosen quotient-image isomorphism.
Source: Stacks 08JA and the fixed K-injective Hom-complex construction.
Proof: since `eN.hom` is an isomorphism, the map induced on H-zero of the integral
global Hom in the second variable is bijective, so `x` is the image of a unique class
`y` in H-zero of the global Hom from `Q(P)` to `Q(N)`. The class map
`coefficientHomZeroClass` of the fixed Hom-section complex is the homology projection
of zero cycles (an epimorphism) followed by the isomorphism of the universal sections
comparison with the fixed K-injective replacement of `N`, as in the proof of
`coefficientHomZeroEquiv_exists`; hence `y` is the class of a zero cycle `z`, and the
image of that class is `x`. No hypothesis on `P` is needed.
(blueprint: lem-coef-derived-sections-normalization-scalar-hom-zero-cycle-surjective)
-/
theorem coefficientDerivedSectionsScalarHomZero_cycle_surjective
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (n : ℕ)
    (M : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (N : CochainComplex (scalarReductionSource l E W) ℤ)
    (eN : DerivedCategory.Q.obj N ≅
      (coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M))
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).obj
      ((coefficientIntegralGlobalHom l E W).obj
        (op (DerivedCategory.Q.obj P),
          (coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M)))) :
    ∃ z : (coefficientHomSectionComplex.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) P N).cycles 0,
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
          ((coefficientIntegralGlobalHom l E W).map
            (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) eN.hom))
        (coefficientHomZeroClass.{u, t + 1, t, max (t + 2) (u + 1)} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P N z) = x := by
  let J := Scheme.ProEt.topology W
  let A := completedIntegralCommRingSheafUnrestricted l E W
  have : IsGrothendieckAbelian.{max u (t + 1)} (scalarReductionSource l E W) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
      J A).1
  let I := coefficientHomResolution.{u, t + 1, t} J A
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0
  let Γ := coefficientGlobalSections.{u, t + 1, t} J A
  let K := coefficientHomSectionComplex.{u, t + 1, t} J A P N
  let γ := zeroHomSectionsComparisonNatTrans.{u, t + 1, t, max (t + 2) (u + 1)} J A I
  have hI (L : CochainComplex (scalarReductionSource l E W) ℤ) :
      (I.obj L).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj _ L
  have : IsIso (γ.app (op P, N)) :=
    zeroHomSectionsComparison_isIso.{u, t + 1, t, max (t + 2) (u + 1)} J A I hI P N
  let c := coefficientHomResolutionIso.{u, t + 1, t, max (t + 2) (u + 1)} J A P N
  let f := H.map ((coefficientIntegralGlobalHom l E W).map
    (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) eN.hom))
  have : IsIso f := by
    let e := (Iso.refl (op (DerivedCategory.Q.obj P))).prod eN
    change IsIso (H.map ((coefficientIntegralGlobalHom l E W).map e.hom))
    infer_instance
  have : IsIso (H.map (Γ.map c.inv)) := (H.mapIso (Γ.mapIso c)).isIso_inv
  have hπ : Epi (K.homologyπ 0) := inferInstance
  have hγepi : Epi (γ.app (op P, N)) := IsIso.epi_of_iso _
  have hcepi : Epi (H.map (Γ.map c.inv)) := IsIso.epi_of_iso _
  have hfepi : Epi f := IsIso.epi_of_iso _
  let q := K.homologyπ 0 ≫ γ.app (op P, N) ≫ H.map (Γ.map c.inv) ≫ f
  have : Epi q := epi_comp' hπ (epi_comp' hγepi (epi_comp' hcepi hfepi))
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective q).mp inferInstance x
  refine ⟨z, ?_⟩
  have hγ := ConcreteCategory.congr_hom
    (zeroHomSectionsComparisonNatTrans_app.{u, t + 1, t, max (t + 2) (u + 1)}
      J A I P N) (K.homologyπ 0 z)
  have hβ := zeroSectionsHomologyComparisonNatTrans_site_apply.{u, t + 1, t,
    max (t + 2) (u + 1)} J A (homComplex (R := A) P (I.obj N))
      (K.homologyπ 0 z)
  have hclass : coefficientHomZeroClass.{u, t + 1, t, max (t + 2) (u + 1)}
      J A P N z = H.map (Γ.map c.inv) (γ.app (op P, N) (K.homologyπ 0 z)) := by
    rw [hγ.trans hβ]
    simp only [coefficientHomZeroClass, Functor.map_comp, AddCommGrpCat.comp_apply]
    rfl
  change f (coefficientHomZeroClass.{u, t + 1, t, max (t + 2) (u + 1)} J A P N z) = x
  rw [hclass]
  exact hz

end WeilConjectures
