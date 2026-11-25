/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomMonoidalData
public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarMonoidal
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarNormalizations

/-! # Generic scalar monoidality with the finite-Hom interface

Share the site-category instances before specializing to finite coefficient quotients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u a₁ a₂ b₁ b₂
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace WeilConjectures

private theorem domainMonoidal_of_core
    {C : Type a₁} {C' : Type a₂} [Category.{b₁} C] [Category.{b₂} C']
    [MonoidalCategory C] [MonoidalCategory C'] (F : C ⥤ C')
    (δ : ∀ U V : C, F.obj (U ⊗ V) ≅ F.obj U ⊗ F.obj V)
    (e : F.obj (𝟙_ C) ≅ 𝟙_ C')
    (β : ∀ U V : C, U ⊗ V ≅ V ⊗ U) (β' : ∀ U V : C', U ⊗ V ≅ V ⊗ U)
    (hc : ∃ c : F.CoreMonoidal,
      c.εIso.symm = e ∧ (∀ U V, (c.μIso U V).symm = δ U V) ∧
      (∀ U V, (β' (F.obj U) (F.obj V)).hom ≫ (c.μIso V U).hom =
        (c.μIso U V).hom ≫ F.map (β U V).hom)) :
    FiniteHomDomainMonoidal F δ e β β' := by
  obtain ⟨c, he, ht, hb⟩ := hc
  exact ⟨c, heq_of_eq he, fun U V ↦ heq_of_eq (ht U V),
    β, β', (fun _ _ ↦ HEq.rfl), (fun _ _ ↦ HEq.rfl), hb⟩

/-- The normalized strong monoidal scalar structure in the shared finite-Hom predicate.
Source: Stacks 07A4 and 0FPT
(blueprint: lem-coef-finite-hom-scalar-monoidal).

Proof: take the already proved canonical scalar CoreMonoidal structure. Replace
its unit and tensor equalities by heterogeneous equalities, and choose the actual
Koszul isomorphisms for the two braiding witnesses. Their heterogeneous equalities
are reflexive and their compatibility is the proved scalar braidedness equation.
Pair this structure with the proved all-complex normalization equations. -/
theorem finiteHomScalar_monoidal
    (A B : Type (u + 1)) [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    FiniteHomDomainMonoidal (Etale.scalarExtension φ T)
      (fun U V ↦ (Etale.ExceptionalCoefficients.tensorIso φ T).app (U, V))
      (Etale.ExceptionalCoefficients.unitIso φ T)
      (finiteHomKoszulIso (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (finiteHomKoszulIso (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))) ∧
    Etale.ExceptionalCoefficients.UnitNormalization φ T
      (Etale.ExceptionalCoefficients.unitIso φ T) ∧
    Etale.ExceptionalCoefficients.TensorNormalization φ T
      (Etale.ExceptionalCoefficients.tensorIso φ T) := by
  exact ⟨domainMonoidal_of_core _ _ _ _ _
    (Etale.ExceptionalCoefficients.scalarExtension_coreMonoidal A B φ T),
    Etale.ExceptionalCoefficients.scalarExtension_normalizations φ T⟩

end WeilConjectures
