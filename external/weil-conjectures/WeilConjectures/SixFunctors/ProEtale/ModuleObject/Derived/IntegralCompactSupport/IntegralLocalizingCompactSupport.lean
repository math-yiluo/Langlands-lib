/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralNormalizedComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompatibleComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCartesianCompactSupport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportPreservation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportPullback

/-! # Integral compact support on the ordinary localizing category -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable (k : Type u) [Field k]
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
set_option synthInstance.maxSize 2048

/-- The integral compactly supported direct image restricts to an exact, coproduct
preserving functor on Loc(Dbc), carries Dbc into Dbc, and has normalized compactification,
composition and base-change isomorphisms, restricting to those same constructible objects.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-int-brown,
sk-prop-int-brown-construction.md and its proof
(blueprint: proposition-construction-independence-rf-shriek).

Proof plan:
1. Standing schemes are qcqs, since they are separated and finite type over k.
   det-def-localizing-closure-ctf-equals-bc identifies Dctf with Dbc for O_E, in the
   same ordinary unbounded module-object derived category, hence their Loc closures.
2. proposition-proper-direct-image-extension-zero gives exactness, coproduct preservation,
   and preservation of Dbc and Loc for the quasi-compact open immersion in c.
3. proposition-proper-direct-image-extension-zero--1 supplies the corresponding integral properties
   for the proper leg. Compose these restrictions, their triangle maps, and their
   coproduct comparisons. This includes the empty coproduct and the zero complex.
4. proposition-construction-independence-rf-shriek gives the comparison maps, normalized by the
proper
   counit and open unit, and their identity and cocycle equations. Fullness of Dbc
   and preservation in step 3 restrict the very same comparisons to Dbc.
5. lem-sfb-nonrational-localizing-lower-shriek-composition, specialized to O_E, gives
   the natural composition isomorphisms, compatible with these comparisons. Step 3
   lets them restrict to Dbc as well.
6. proposition-composition-base-change-rf-shriek--4 gives the proper exchange followed by inverse
   open exchange, and its compatibility with compactification comparisons. The locus
   of invertibility is localizing, so invertibility on generators suffices. Finally
   lemma-inverse-image-tensor-product supplies pullback preservation of Dbc. Since pullback is exact
   and preserves coproducts, it preserves Loc too, giving the base-change functors
   and the restriction of the same isomorphisms to Dbc. -/
theorem integralLocalizingCompactSupport (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    ∃ (h : Preservation (Profinite.padicIntegersRingObj ℓ E.val) k)
      (φ : Comparisons (Profinite.padicIntegersRingObj ℓ E.val) k)
      (μ : Compositions (Profinite.padicIntegersRingObj ℓ E.val) k),
      Coherence (Profinite.padicIntegersRingObj ℓ E.val) k h φ μ := by
  obtain ⟨φ, hi, hc, hn⟩ := normalizedComparisons k ℓ E
  have h := preservation_of_ctf_eq k ℓ E
  obtain ⟨μ, hm⟩ := compatibleComposition k ℓ E h φ hi hc hn
  have hp := fun {X Y : Spaces k} (v : X ⟶ Y) ↦ pullback_of_ctf_eq k ℓ E v
  obtain ⟨hb, hbc⟩ := cartesianCompactSupport k ℓ E h φ hi hc hn
    (fun v ↦ (hp v).2)
  exact ⟨h, φ, μ, ⟨hi, hc, hn, hm, fun v ↦ (hp v).1,
    fun v ↦ (hp v).2, hb, hbc⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
