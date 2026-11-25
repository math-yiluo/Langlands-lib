/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsHom
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Finiteness

/-!
# Compactly supported cohomology in degree zero

For a Weil sheaf `G` on a separated `k₀`-scheme `X` of finite type, with the compactification
`X ⟶[i] Z ⟶[g] Spec k₀` used to define `Ra_! = Rḡ_* ∘ ī_!`, the degree-zero compactly
supported cohomology is `H⁰(Spec k̄, Rḡ_* ī_! G) = Γ(Z̄, ī_! G)`, the global sections of the
extension by zero of `G` to the compactification. Hence `H_c^0(X, G)` vanishes as soon as every
global section `ℚ̄_ℓ ⟶ ī_! G` vanishes
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero_of_forall_eq_zero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

attribute [local instance] AlgebraicGeometry.Compactification.over

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The degree-zero compactly supported cohomology `H_c^0(X, G) = Γ(Z̄, ī_! G)` of a Weil sheaf
vanishes if, for every compactification `X ⟶[i] Z ⟶ Spec k₀`, every global section
`ℚ̄_ℓ ⟶ ī_! G` of the extension by zero to the geometric fiber of `Z` vanishes. -/
theorem WeilSheaf.subsingleton_compactlySupportedCohomology_zero_of_forall_eq_zero
    (G : WeilSheaf k₀ l X)
    (hG : ∀ (c : Compactification (X ↘ Spec (CommRingCat.of k₀)))
      (β : ProEtale.AdicSheaf.unit l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
        (Scheme.Hom.geometricFiberMap c.i (comp_over c.i _))_!ᵃ[l].obj G.obj.carrier), β = 0) :
    Subsingleton (G.compactlySupportedCohomology 0).carrier := by
  let c := HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)
  let E := ProEtaleWeilSheaf.extensionByZero k₀ l c.i
  let e : ((WeilComplex.homologySheaf 0).obj ((WeilComplex.derivedLowerShriek k₀ l
      (X ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj G))).obj ≅
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g).obj (E.obj G.obj) :=
    (_root_.DerivedCategory.homologyFunctor _ 0).mapIso
      ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
        ((E.mapDerivedCategorySingleFunctor 0).app G.obj)) ≪≫
    (ProEtaleWeilSheaf.lowerStar k₀ l c.g).homologyRightDerivedFunctorObjSingleFunctorIso
      (E.obj G.obj) 0 ≪≫
    (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedZeroIsoSelf.app _
  let e' := (Sheaf.Γ _ (WeilCoefficients.{u} l)).mapIso ((ProEtale.AdicSheaf.forget _).mapIso
      ((IsoAlgebra.forget _).mapIso e)) ≪≫
    (ProEtale.globalSectionsLowerStarIso _ (Scheme.Hom.geometricFiberMap c.g
      (comp_over c.g _))).app _
  have : Subsingleton ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
        ((Scheme.Hom.geometricFiberMap c.i (comp_over c.i _))_!ᵃ[l].obj G.obj.carrier).X)) := by
    refine ⟨fun a b ↦ ?_⟩
    obtain ⟨β, rfl⟩ := (ProEtale.bijective_globalSectionOfModHom _).2 a
    obtain ⟨β', rfl⟩ := (ProEtale.bijective_globalSectionOfModHom _).2 b
    rw [hG c β, hG c β']
  exact @Equiv.subsingleton _ _ (WeilCoefficients.linearEquivOfIso e').toEquiv this

end AlgebraicGeometry
