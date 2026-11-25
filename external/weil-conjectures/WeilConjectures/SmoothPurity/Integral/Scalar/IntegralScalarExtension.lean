/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
public import WeilConjectures.SixFunctors.Integral.IntegralDerivedReductionSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import all WeilConjectures.Algebra.Homology.Finite.FiniteFreeScalarExtension

/-! # Completed integral scalar extension

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460; Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- Completed extension, obtained by the universal localization of the specified
strict Roos construction on K-flat complexes with flat terms. The construction has
actual data: its tower, transition maps and diagonal cone maps are those of
`integralScalarOnGood`, not arbitrary maps between homotopy limits.
Source: blueprint order 1460; Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable def integralScalarExtension :
    DerivedCategory (integralTowerModules l E Y) ⥤
      DerivedCategory (integralTowerModules l L Y) :=
  (integralScalarExtensionWellDefined l E L ι Y).2.choose

/-- The representative comparison is part of the universal localization datum.
Source: blueprint order 1460; Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable def integralScalarExtensionComparison :
    integralOperationsGoodLocalization l E Y ⋙ integralScalarExtension l E L ι Y ≅
      integralScalarOnGood l E L ι Y :=
  (integralScalarExtensionWellDefined l E L ι Y).2.choose_spec.choose

/-- Additivity of the specified completed extension.
Source: blueprint order 1460 (blueprint: def-weil-integral-scalar-extension). -/
noncomputable instance integralScalarExtension_additive :
    (integralScalarExtension l E L ι Y).Additive :=
  (integralScalarExtensionWellDefined l E L ι Y).2.choose_spec.choose_spec.1

end WeilConjectures

namespace WeilConjectures

open CategoryTheory CategoryTheory.Limits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The completed coefficient map, uniquely fixed by its finite quotient projections.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension).
Proof: the quotient inclusion maps commute with reduction. The limit universal property
therefore gives the completed map; joint monicity of its projections gives uniqueness. -/
theorem integralCompletedScalarMap_existsUnique :
    ∃! φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
        completedIntegralCommRingSheafUnrestricted l L Y,
      ∀ n : ℕ, φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
        integralScalarRho l E L ι Y n := by
  let forgetComm := sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let α : integralCoefficientSheafSystem l E Y ⟶
      integralCoefficientSheafSystem l L Y :=
    NatTrans.ofOpSequence
      (fun n ↦ forgetComm.map (integralScalarQuotientSheafMap l E L ι Y n))
      (by
        intro n
        simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
        change integralCoefficientSheafTransition l E Y n ≫ _ =
          _ ≫ integralCoefficientSheafTransition l L Y n
        unfold integralCoefficientSheafTransition integralScalarQuotientSheafMap
        change forgetComm.map _ ≫ forgetComm.map _ =
          forgetComm.map _ ≫ forgetComm.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 2
        ext x
        exact RingHom.congr_fun (integralScalarQuotientMap_transition l E L ι n).symm x.down)
  let c : Cone (integralCoefficientSheafSystem l L Y) :=
    { pt := completedIntegralCoefficientSheafUnrestricted l E Y
      π := (limit.cone (integralCoefficientSheafSystem l E Y)).π ≫ α }
  let φr := limit.lift (integralCoefficientSheafSystem l L Y) c
  let φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y :=
    forgetComm.preimage
      (X := completedIntegralCommRingSheafUnrestricted l E Y)
      (Y := completedIntegralCommRingSheafUnrestricted l L Y) φr
  have hproj (F : Type u) [Field F] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] F] (n : ℕ) :
      forgetComm.map (completedIntegralCommRingProjectionUnrestricted l F Y n) =
        limit.π (integralCoefficientSheafSystem l F Y) (Opposite.op n) := by
    ext U x
    rfl
  have hφ (n : ℕ) :
      φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
        completedIntegralCommRingProjectionUnrestricted l E Y n ≫
          integralScalarQuotientSheafMap l E L ι Y n := by
    apply forgetComm.map_injective
    rw [Functor.map_comp, Functor.map_comp, hproj, hproj]
    dsimp only [φ]
    rw [Functor.map_preimage]
    exact limit.lift_π c (Opposite.op n)
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply forgetComm.map_injective
  apply limit.hom_ext
  intro n
  have h := congrArg forgetComm.map ((hψ n.unop).trans (hφ n.unop).symm)
  simpa only [Functor.map_comp, hproj] using h

/-- The actual map of completed coefficient rings, fixed at every finite level.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable def integralCompletedScalarMap :
    completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y :=
  (integralCompletedScalarMap_existsUnique l E L ι Y).exists.choose

/-- The ordinary tensor functor with its prescribed object and morphism formulas.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension).
Proof: use the sectionwise balanced tensor map on each sheaf morphism and then
sheafify. The tensor identity and composition equations descend by the universal
property of sheafification. Additivity holds on tensor generators and hence locally
on all sections. Both objects and maps are specified, so no arbitrary functor is chosen. -/
theorem integralOrdinaryScalarWitness :
    ∃ (F : integralTowerModules.{u, u} l E Y ⥤ integralTowerModules.{u, u} l L Y)
      (h : ∀ N, F.obj N = SheafOfModules.changeOfRings
        (integralCompletedScalarMap l E L ι Y) N)
      (_ : ∀ {N N' : integralTowerModules.{u, u} l E Y} (f : N ⟶ N'),
        F.map f = eqToHom (h N) ≫ SheafOfModules.changeOfRingsHom
          (integralCompletedScalarMap l E L ι Y) N f ≫ eqToHom (h N').symm)
      , F.Additive := by
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{u + 1} := integralCoefficientAbSheafify.{u, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} Y
  obtain ⟨F, hobj, hmap, hadd, _⟩ :=
    SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (O := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y)
      (O' := completedIntegralCommRingSheafUnrestricted.{u, u} l L Y)
      (integralCompletedScalarMap l E L ι Y)
  exact ⟨F, hobj, hmap, hadd⟩

/-- Ordinary tensor with the finite free completed coefficient extension.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable def integralOrdinaryScalar :
    integralTowerModules.{u, u} l E Y ⥤ integralTowerModules.{u, u} l L Y :=
  (integralOrdinaryScalarWitness l E L ι Y).choose

/-- Additivity of ordinary extension of scalars.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable instance integralOrdinaryScalar_additive :
    (integralOrdinaryScalar l E L ι Y).Additive :=
  (integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose_spec.choose_spec

private theorem integralOrdinaryScalar_obj (M : integralTowerModules l E Y) :
    (integralOrdinaryScalar l E L ι Y).obj M =
      SheafOfModules.changeOfRings (integralCompletedScalarMap l E L ι Y) M := by
  exact (integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose M

private theorem integralOrdinaryScalar_map
    {M N : integralTowerModules l E Y} (f : M ⟶ N) :
    (integralOrdinaryScalar l E L ι Y).map f =
      eqToHom (integralOrdinaryScalar_obj l E L ι Y M) ≫
        SheafOfModules.changeOfRingsHom (integralCompletedScalarMap l E L ι Y) M f ≫
          eqToHom (integralOrdinaryScalar_obj l E L ι Y N).symm := by
  exact (integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose_spec.choose f

private theorem integralCompletedScalarMap_projection (n : ℕ) :
    integralCompletedScalarMap l E L ι Y ≫
        completedIntegralCommRingProjectionUnrestricted l L Y n =
      integralScalarRho l E L ι Y n := by
  exact (integralCompletedScalarMap_existsUnique l E L ι Y).exists.choose_spec n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteFreeOrdinary_exact
    {C : Type u} [Category* C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (hobj : ∀ M, F.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm) :
    PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  let A := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let B := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S
  let U := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let α : F ⋙ U ≅ finitePowerFunctor (A := SheafOfModules.{u} A) d :=
    NatIso.ofComponents (fun M ↦ U.mapIso (eqToIso (hobj M)) ≪≫
      SheafOfModules.scalarExtensionIso φ d e M) (by
        intro M N f
        change U.map (F.map f) ≫ (U.map (eqToHom (hobj N)) ≫ _) =
          (U.map (eqToHom (hobj M)) ≫ _) ≫ _
        rw [hmap f, Functor.map_comp, Functor.map_comp]
        simp only [Category.assoc, ← U.map_comp_assoc, eqToHom_trans, eqToHom_refl,
          U.map_id, Category.id_comp]
        exact congrArg (fun k ↦ U.map (eqToHom (hobj M)) ≫ k)
          (SheafOfModules.scalarExtensionIso_naturality φ d e f))
  have : PreservesFiniteLimits U := by
    have : PreservesFiniteLimits (U ⋙ SheafOfModules.toSheaf A) :=
      inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} B))
    have : ReflectsFiniteLimits (SheafOfModules.toSheaf.{u} A) :=
      reflectsFiniteLimits_of_reflectsIsomorphisms _
    exact preservesFiniteLimits_of_reflects_of_preserves U (SheafOfModules.toSheaf A)
  have : PreservesFiniteColimits U := by
    have : PreservesFiniteColimits (U ⋙ SheafOfModules.toSheaf A) :=
      inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} B))
    have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u} A) :=
      reflectsFiniteColimitsOfReflectsIsomorphisms _
    exact preservesFiniteColimits_of_reflects_of_preserves U (SheafOfModules.toSheaf A)
  have : U.ReflectsIsomorphisms := by
    have : (U ⋙ SheafOfModules.toSheaf A).ReflectsIsomorphisms :=
      inferInstanceAs (SheafOfModules.toSheaf.{u} B).ReflectsIsomorphisms
    exact reflectsIsomorphisms_of_comp U (SheafOfModules.toSheaf A)
  have : PreservesFiniteLimits (finitePowerFunctor (A := SheafOfModules.{u} A) d) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits (F ⋙ U) := preservesFiniteLimits_of_natIso α.symm
  have : PreservesFiniteColimits (F ⋙ U) := preservesFiniteColimits_of_natIso α.symm
  have : ReflectsFiniteLimits U := reflectsFiniteLimits_of_reflectsIsomorphisms _
  have : ReflectsFiniteColimits U := reflectsFiniteColimitsOfReflectsIsomorphisms _
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F U,
    preservesFiniteColimits_of_reflects_of_preserves F U⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite coefficient extensions are finite free, so their ordinary sheaf tensor is exact.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: def-weil-integral-scalar-extension).
Proof: O_L is finite free over O_E. Choose an integral basis only in the proof. Tensor
with that finite free module commutes with the finite coefficient limits defining the
completed sheaf, since finite products and finite sums agree for modules. Thus the
completed coefficient extension is finite locally free. Sectionwise tensor followed by
exact sheafification is exact. Its adjunction gives preservation of finite colimits,
and flatness gives preservation of finite limits. No geometric finiteness is used. -/
theorem integralOrdinaryScalar_exact :
    PreservesFiniteLimits (integralOrdinaryScalar l E L ι Y) ∧
      PreservesFiniteColimits (integralOrdinaryScalar l E L ι Y) := by
  classical
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{u + 1} := integralCoefficientAbSheafify.{u, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} Y
  let φ := integralCompletedScalarMap l E L ι Y
  let := ι.toAlgebra
  obtain ⟨e⟩ := completedIntegralFiniteFree.{u, u} l E Y L ι φ
    (integralCompletedScalarMap_projection l E L ι Y)
  exact finiteFreeOrdinary_exact φ (Module.finrank E L) e.symm
    (integralOrdinaryScalar l E L ι Y) (integralOrdinaryScalar_obj l E L ι Y)
    (fun f ↦ integralOrdinaryScalar_map l E L ι Y f)

/-- Exactness on finite limits. Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable instance integralOrdinaryScalar_finiteLimits :
    PreservesFiniteLimits (integralOrdinaryScalar l E L ι Y) :=
  (integralOrdinaryScalar_exact l E L ι Y).1

/-- Exactness on finite colimits. Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable instance integralOrdinaryScalar_finiteColimits :
    PreservesFiniteColimits (integralOrdinaryScalar l E L ι Y) :=
  (integralOrdinaryScalar_exact l E L ι Y).2

/-- Exact ordinary extension, computed termwise on derived complexes. On complete
objects this is the completed scalar extension; that assertion is recorded separately.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable abbrev integralOrdinaryDerivedScalar :=
  (integralOrdinaryScalar l E L ι Y).mapDerivedCategory

end WeilConjectures
