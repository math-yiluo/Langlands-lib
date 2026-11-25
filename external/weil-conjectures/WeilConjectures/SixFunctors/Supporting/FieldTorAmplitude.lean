/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude

import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.StratifiedTorIntervalDevissage
import WeilConjectures.AlgebraicGeometry.CohomologyTorInterval
import Mathlib.Algebra.Field.ULift
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.SmoothPurity.ConstantFieldTensorCohomology

/-! # Finite Tor amplitude at condensed field coefficients

Source: current blueprint `proposition-ctf-equals-bc`, field case of clause (2).
This specializes the local-model and truncation argument to the two field coefficient
families, in the ordinary derived category over the pulled-back condensed ring.
(blueprint: lem-weil-field-tor-amplitude).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

section DiscreteField

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory.Limits MonoidalCategory in
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- A bounded complex over a discrete constant field has Tor amplitude in its
cohomological interval. This existing helper is retained for the residue-field consumers.

Source: Stacks Project, Tags 08FZ and 010N; constant-field tensor cohomology
`lem-exc-constant-field-sheaf-tensor-cohomology`.
(blueprint: lem-weil-field-tor-amplitude).

Proof: a quasi-isomorphic representative has the same cohomology as `K`. Exact tensor
over the constant field commutes with cohomology. The sheafification counit and tensorator
identify this exact tensor with the tensor used by `derivedTensor`, and the comparison
with the total complex having one degree-zero factor gives the asserted vanishing. -/
theorem bounded_field_tor (Y : Scheme.{u}) (A : Type u) [Field A]
    (K : proEtaleDerivedCategory Y A) (a b : ℤ) (hab : a ≤ b)
    (hK : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    HasProEtaleTorAmplitude Y A K a b := by
  classical
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let R := (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} A))
  let C := SheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let := HasDerivedCategory.standard C
  let := SheafOfModules.cochainTensorLocalizationIsMonoidal.{u + 1, u, u + 1}
    (C := Y.ProEt) (J := ProEt.topology Y) R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  change a ≤ b ∧ _
  refine ⟨hab, ?_⟩
  intro L P hL f hf hP M i hi
  have : QuasiIso f := hf
  obtain ⟨eL⟩ := hL
  have hPi : IsZero (P.homology i) := by
    let e := (DerivedCategory.homologyFunctor C i).mapIso
      (asIso (DerivedCategory.Q.map f) ≪≫ eL)
    exact ((hK i hi).of_iso e).of_iso
      ((DerivedCategory.homologyFunctorFactors C i).app P).symm
  obtain ⟨e, _⟩ := SheafOfModules.exists_constantFieldTensorCohomology
    (ProEt.topology Y) (ULift.{u + 1} A) i
  have hz := ((SheafOfModules.siteSheafTensorRight M).map_isZero hPi).of_iso (e M P).symm
  let T := (tensorRight M).mapHomologicalComplex (.up ℤ)
  let S := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let F := PresheafOfModules.sheafification.{u + 1} (𝟙 S.obj)
  let p (N : PresheafOfModules.{u + 1} S.obj) :
      (N ⊗ M.val : PresheafOfModules.{u + 1} S.obj) ≅
        SheafOfModules.siteTensorPresheaf N M.val :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro U V f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      rfl)
  let V := SheafOfModules.forget S
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)
  let e := asIso adj.counit
  let c₁ : tensorRight M ≅ V ⋙ tensorRight M.val ⋙ F :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight e.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft V
        (Functor.isoWhiskerLeft F ((curriedTensor C).flip.mapIso (e.app M).symm) ≪≫
          Functor.Monoidal.commTensorRight F M.val)
  let q : tensorRight M.val ≅ SheafOfModules.siteTensorRight M.val :=
    NatIso.ofComponents p (by
      intro N N' f
      ext U : 1
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      rfl)
  let c := c₁ ≪≫ Functor.isoWhiskerLeft V (Functor.isoWhiskerRight q F)
  have : (V ⋙ SheafOfModules.siteTensorRight M.val ⋙ F).PreservesZeroMorphisms := by
    change (SheafOfModules.siteSheafTensorRight M).PreservesZeroMorphisms
    infer_instance
  have ht : IsZero ((T.obj P).homology i) :=
    hz.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso
      ((NatIso.mapHomologicalComplex c (.up ℤ)).app P))
  let t := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) M P
  exact (ht.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso t)).of_iso
    ((DerivedCategory.homologyFunctorFactors C i).app _)

end DiscreteField

end WeilConjectures
