/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement

/-! # Conjugating finite coefficient derived direct images

The underived encoding comparison is already constructed in
`FiniteDiscreteRestrictionEncoding`. Derive it using the exact coefficient equivalences.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance] coefficientProfiniteEssentiallySmall

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
variable (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

/-- The explicit finite coefficient equivalences conjugate bounded-below direct image.
Source: Bhatt--Scholze, Lemmas 5.4.1 and 5.4.3; Stacks Project, Tag 099R
(blueprint: lem-weil-pbc-finite-discrete-coefficient-direct-image-conjugation).

Proof in words. Expand the common coefficient equivalence into the sectionwise module
encoding and the inverse of the constant-ring restriction equivalence. Sectionwise
restriction commutes with the fixed additive equivalence by `hG`, while the scalar
maps commute by naturality of the coefficient-ring map pulled back from the profinite
point. This gives an underived natural isomorphism between internal pushforward after
encoding and encoding after module-valued pushforward. The encoding equivalences are
exact, so applying the right-derived functor construction transports this isomorphism
to the displayed bounded-below derived categories. -/
theorem finiteDiscreteCoefficient_directImage_conjugation [DiscreteTopology B] [Finite B]
    {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h] :
    ∀ X : DerivedCategory.Plus (FiniteDiscreteProEtaleSheaves B S),
      Nonempty (
        (D((finiteDiscreteCoefficientEquivalence B eR G hG T).functor)).obj
            (DerivedCategory.Plus.ι.obj
              ((R+(ProEtale.lowerStar
                (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)).obj X)) ≅
        (coefficientDerivedLowerStar (Profinite.continuousMapRingObj B) h).obj
          ((D((finiteDiscreteCoefficientEquivalence B eR G hG S).functor)).obj
            (DerivedCategory.Plus.ι.obj X))) := by
  intro X
  let ES := finiteDiscreteCoefficientEquivalence B eR G hG S
  let ET := finiteDiscreteCoefficientEquivalence B eR G hG T
  let H := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h
  let I := lowerStar (Profinite.continuousMapRingObj B) h
  -- The sectionwise action calculation has already been proved in the encoding module.
  let i := encodingPushforwardNatIso B eR G hG T S h
  let j : (ES.functor ⋙ I) ⋙ ET.inverse ≅ H :=
    Functor.associator _ _ _ ≪≫ Iso.inverseCompIso (G := ES.symm) i
  let k : H ⋙ ET.functor ≅ ES.functor ⋙ I :=
    (Iso.isoCompInverse (H := ET.symm) j).symm
  -- Equivalences are exact and preserve K-injective complexes.
  let d : R(H) ⋙ D(ET.functor) ≅ D(ES.functor) ⋙ R(I) :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso H ET.functor).symm ≪≫
      Functor.rightDerivedFunctorNatIso k ≪≫
      Functor.rightDerivedFunctorCompIso ES.functor I ≪≫
      Functor.isoWhiskerRight ES.functor.rightDerivedFunctorIsoMapDerivedCategory R(I)
  -- Include the bounded-below direct image in the unbounded derived category.
  exact ⟨D(ET.functor).mapIso (H.rightDerivedFunctorPlusCompatibility.app X) ≪≫
    d.app (DerivedCategory.Plus.ι.obj X)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
