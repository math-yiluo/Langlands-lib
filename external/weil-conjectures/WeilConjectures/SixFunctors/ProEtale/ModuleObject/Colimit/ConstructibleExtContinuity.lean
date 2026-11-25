/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissage
public import WeilConjectures.CategoryTheory.Abelian.HomologyFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralFlat
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-!
# Continuity of `Hom` out of a bounded constructible `E`-complex

For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, a topologically noetherian scheme `X` and a bounded
constructible complex `C ∈ Dᵇc(X)⟦E̲⟧`, morphisms in `D(X_proét, E)` from `C` to a filtered
colimit `K = colim_j K_j` of complexes of `E_X`-modules which all vanish below a fixed degree are
the filtered colimit of the morphisms `C ⟶ K_j`, in every shift
(`ProEtale.CondensedRing.constructibleExtContinuity_continuousMapRingObj`, blueprint
`lemma-continuity-ext-out-constructible-complex--1` (1)).

## Proof

Following the blueprint, the class of objects `s` such that `Hom(s, -[n])` commutes with filtered
colimits of `E_X`-modules is closed under shifts and extensions; by dévissage
(`ProEtale.prop_of_boundedConstructibleModule`) it contains `Dᵇc(X, E)` as soon as it contains the
constructible sheaves, which is
`homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject`
(reducing to lisse, hence locally free, sheaves:
`ProEtale.CondensedRing.homCommutesWithFilteredColimits_singleFunctor_continuousMapRingObj`).
Since `C` is bounded above, the continuity extends to filtered colimits of uniformly bounded below
complexes (`DerivedCategory.HomCommutesWithFilteredColimits.cochainComplex`), filtered colimits of
`E_X`-modules being exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A bounded constructible complex is bounded above. -/
lemma BoundedConstructible.exists_isLE {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) A} [MonObj R] [IsCommMonObj R]
    (K : BoundedConstructible R) : ∃ b : ℤ, K.obj.IsLE b := by
  obtain ⟨-, ⟨b, hb⟩⟩ := K.property.1
  exact ⟨b, hb⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- Blueprint `lemma-continuity-ext-out-constructible-complex--1`, lisse case for `E`: on a scheme
with noetherian underlying space, `Hom(L[0], -[n])` commutes with filtered colimits for every
locally finitely presented `E_X`-module `L`, which is locally free. -/
theorem homCommutesWithFilteredColimits_singleFunctor_continuousMapRingObj (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X))
    (hL : IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj E) X) L) :
    DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}
      ((DerivedCategory.singleFunctor _ 0).obj L) :=
  have := preservesFiniteLimits_tensorLeft_continuousMapRingObj_of_finiteDimensional ℓ E X
  homCommutesWithFilteredColimits_singleFunctor_of_isLocallyFree _ X (continuous_lf ℓ E X L hL)

open ZeroObject in
/-- Blueprint `lemma-continuity-ext-out-constructible-complex--1` (1), for targets in degree `0`: on
a scheme with noetherian underlying space, `Hom(C, -[n])` out of a bounded constructible `E`-complex
`C` commutes with filtered colimits of `E_X`-modules. By dévissage
(`ProEtale.prop_of_boundedConstructibleModule`) it suffices to treat constructible sheaves, which
is `homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject`. -/
theorem homCommutesWithFilteredColimits_of_boundedConstructible_continuousMapRingObj
    [TopologicalSpace.NoetherianSpace X] (C : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧) :
    DerivedCategory.HomCommutesWithFilteredColimits.{u + 1} C.obj := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  let P : ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))) :=
    fun s ↦ DerivedCategory.HomCommutesWithFilteredColimits.{u + 1} s
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ h.of_iso e⟩
  have : P.IsTriangulated :=
    { exists_zero := ⟨_, isZero_zero _, .of_isZero (isZero_zero _)⟩
      isStableUnderShiftBy a := ⟨fun s hs ↦ hs.shift a⟩
      ext₂' T hT h₁ h₃ := P.le_isoClosure _ (.ext₂ T hT h₁ h₃) }
  exact prop_of_boundedConstructibleModule P (fun F hF ↦
    homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject _
      (preservesFiniteLimits_tensorLeft_continuousMapRingObj_of_finiteDimensional ℓ E.1)
      (fun _ _ ↦ homCommutesWithFilteredColimits_singleFunctor_continuousMapRingObj ℓ E.1 _)
      X F hF) C.property

/-- Blueprint `lemma-continuity-ext-out-constructible-complex--1` (1), for the coefficient ring `E̲`
of a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`. Let `X` be a topologically noetherian scheme,
`C ∈ Dᵇc(X, E)`, and `K = colim_j K_j` a filtered colimit of complexes of `E_X`-modules all of
which vanish below a fixed degree `a`. Then for every `q ∈ ℤ`, the natural map
`colim_j Hom(C, K_j[q]) ⟶ Hom(C, K[q])` is bijective:

* every morphism `C ⟶ K[q]` factors through some `K_j[q]`;
* two morphisms `C ⟶ K_j[q]` with the same image in `Hom(C, K[q])` agree in some
  `Hom(C, K_{j'}[q])`.

The morphisms out of `C` commute with filtered colimits of sheaves
(`homCommutesWithFilteredColimits_of_boundedConstructible_continuousMapRingObj`), hence with
filtered colimits of uniformly bounded below complexes
(`DerivedCategory.HomCommutesWithFilteredColimits.diagram`), since `C` is bounded above and
filtered colimits of `E_X`-modules are exact. -/
theorem constructibleExtContinuity_continuousMapRingObj [TopologicalSpace.NoetherianSpace X]
    (C : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧) {J : Type} [SmallCategory J] [IsFiltered J]
    (K : J ⥤ CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) ℤ)
    (a : ℤ) (hK : ∀ j, (K.obj j).IsStrictlyGE a) (c : Cocone K) (hc : IsColimit c) (q : ℤ) :
    (∀ f : C.obj ⟶ (shiftFunctor _ q).obj (DerivedCategory.Q.obj c.pt),
      ∃ (j : J) (g : C.obj ⟶ (shiftFunctor _ q).obj (DerivedCategory.Q.obj (K.obj j))),
        f = g ≫ (shiftFunctor _ q).map (DerivedCategory.Q.map (c.ι.app j))) ∧
    (∀ (j : J) (g g' : C.obj ⟶ (shiftFunctor _ q).obj (DerivedCategory.Q.obj (K.obj j))),
      g ≫ (shiftFunctor _ q).map (DerivedCategory.Q.map (c.ι.app j)) =
          g' ≫ (shiftFunctor _ q).map (DerivedCategory.Q.map (c.ι.app j)) →
        ∃ (j' : J) (t : j ⟶ j'),
          g ≫ (shiftFunctor _ q).map (DerivedCategory.Q.map (K.map t)) =
            g' ≫ (shiftFunctor _ q).map (DerivedCategory.Q.map (K.map t))) := by
  have hC := C.exists_isLE
  have : C.obj.IsLE hC.choose := hC.choose_spec
  exact (homCommutesWithFilteredColimits_of_boundedConstructible_continuousMapRingObj X ℓ E
    C).cochainComplex hC.choose K a hK c hc q

end AlgebraicGeometry.ProEtale.CondensedRing
