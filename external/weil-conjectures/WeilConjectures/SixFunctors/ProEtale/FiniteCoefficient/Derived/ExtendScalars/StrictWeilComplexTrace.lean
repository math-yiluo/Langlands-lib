/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.StrictWeilComplexFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace

/-!
# Finite-level coefficient change of the traces of the Frobenius operators

Let `ρ : R → S` be a homomorphism of finite commutative rings whose exponent is invertible on a
scheme `X` of finite type over a field `k`, and `Ψ = - ⊗ᴸ_R S` derived scalar extension. For a
strict Weil complex `(K, φ)` over `R` with scalar extension `(K_S, φ_S)`, the categorical traces
of the global and local Frobenius operators over `S` are the images under `ρ` of those over `R`
(blueprint `theorem-grothendieck-lefschetz-trace-formula--7`):
```
ρ (tr_R(F_{c,m} ∣ RΓ_c(X, K))) = tr_S(F_{c,m} ∣ RΓ_c(X, K_S)),
ρ (tr_R(F_{x,m} ∣ K_x̄)) = tr_S(F_{x,m} ∣ (K_S)_x̄).
```
Here the traces are taken in `D(Spec k_proét, -)` with the Koszul braidings
`DerivedCategory.braidedCategory'`, and the map `ρ : End(𝟙_R) ⟶ End(𝟙_S)` is
`t ↦ ε ≫ Ψ t ≫ η` for the monoidal structure `leftDerivedSheafExtendScalarsMonoidal` of `Ψ`; it
sends `a • 𝟙` to `ρ a • 𝟙`. Hence the finite-ring trace formula over `R` maps to the
finite-ring trace formula over `S`.

## Main statements

- `AlgebraicGeometry.ProEtale.StrictWeilComplex.trace_globalFrobenius_extendScalars`,
  `AlgebraicGeometry.ProEtale.StrictWeilComplex.trace_globalFrobenius_extendScalars_of_eq_smul`:
  the global traces.
- `AlgebraicGeometry.ProEtale.StrictWeilComplex.trace_localFrobenius_extendScalars`,
  `AlgebraicGeometry.ProEtale.StrictWeilComplex.trace_localFrobenius_extendScalars_of_eq_smul`:
  the local traces.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

namespace StrictWeilComplex

attribute [local instance] DerivedCategory.braidedCategory'

variable {R : Type (u + 1)} [CommRing R] [IsNoetherianRing R] {k : Type u} [Field k]
  {X : Scheme.{u}} {aX : X ⟶ Spec (.of k)} {g : X ≅ X} (c : Compactification aX)
  {gZ : c.Z ⟶ c.Z} (hi : IsPullback g.hom c.i c.i gZ) (hg : CommSq gZ c.g c.g (𝟙 _))
  (S : Type (u + 1)) [CommRing S] [Algebra R S] [Finite R] [Finite S]
  [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent R X]

/-- **Coefficient change of the global traces** (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`):
`tr_S(F_{c,m} ∣ RΓ_c(X, K_S)) = ρ (tr_R(F_{c,m} ∣ RΓ_c(X, K)))`, where `ρ t = ε ≫ Ψ t ≫ η` is
induced by the monoidal functor `Ψ = - ⊗ᴸ_R S`. -/
theorem trace_globalFrobenius_extendScalars (W : StrictWeilComplex (ModuleCat.{u + 1} R) g)
    (m : ℕ) [HasRightDual (Rf_!(c)[ModuleCat.{u + 1} R].obj W.obj.obj)]
    [HasRightDual (Rf_!(c)[ModuleCat.{u + 1} S].obj (W.extendScalars S aX).obj.obj)]
    [HasRightDual (L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).obj
      (Rf_!(c)[ModuleCat.{u + 1} R].obj W.obj.obj))] :
    letI := leftDerivedSheafExtendScalarsMonoidal (R := R) (S := S) (Spec (.of k))
    trace ((W.extendScalars S aX).globalFrobenius c hi hg m) =
      ε L(sheafExtendScalars (algebraMap R S) (Spec (.of k))) ≫
        L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).map
          (trace (W.globalFrobenius c hi hg m)) ≫
        η L(sheafExtendScalars (algebraMap R S) (Spec (.of k))) := by
  have := isIso_rightDerivedLowerShriekOfCompactificationExtendScalarsMap_app R S c
    W.obj.property
  let : HasRightDual ((Rf_!(c)[ModuleCat.{u + 1} R] ⋙
      L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).obj W.obj.obj) :=
    inferInstanceAs (HasRightDual (L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).obj
      (Rf_!(c)[ModuleCat.{u + 1} R].obj W.obj.obj)))
  let : HasRightDual ((L(sheafExtendScalars (algebraMap R S) X) ⋙
      Rf_!(c)[ModuleCat.{u + 1} S]).obj W.obj.obj) :=
    inferInstanceAs (HasRightDual (Rf_!(c)[ModuleCat.{u + 1} S].obj
      (W.extendScalars S aX).obj.obj))
  rw [← trace_leftDerivedSheafExtendScalars_map]
  exact (trace_eq_of_iso
    (asIso ((rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app W.obj.obj))
    _ _ (globalFrobenius_extendScalars c hi hg S W m)).symm

/-- **Coefficient change of the global traces, for scalar traces**: if
`tr_R(F_{c,m} ∣ RΓ_c(X, K)) = a • 𝟙`, then `tr_S(F_{c,m} ∣ RΓ_c(X, K_S)) = ρ a • 𝟙`. -/
theorem trace_globalFrobenius_extendScalars_of_eq_smul
    (W : StrictWeilComplex (ModuleCat.{u + 1} R) g) (m : ℕ)
    [HasRightDual (Rf_!(c)[ModuleCat.{u + 1} R].obj W.obj.obj)]
    [HasRightDual (Rf_!(c)[ModuleCat.{u + 1} S].obj (W.extendScalars S aX).obj.obj)]
    [HasRightDual (L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).obj
      (Rf_!(c)[ModuleCat.{u + 1} R].obj W.obj.obj))] {a : R}
    (ha : trace (W.globalFrobenius c hi hg m) = a • 𝟙 _) :
    trace ((W.extendScalars S aX).globalFrobenius c hi hg m) = algebraMap R S a • 𝟙 _ := by
  rw [trace_globalFrobenius_extendScalars c hi hg S W m, ha]
  exact ε_comp_leftDerivedSheafExtendScalars_map_smul_id_comp_η _ a

/-- **Coefficient change of the local traces** (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`):
`tr_S(F_{x,m} ∣ (K_S)_x̄) = ρ (tr_R(F_{x,m} ∣ K_x̄))` at a point `x` fixed by `g^m`, where
`ρ t = ε ≫ Ψ t ≫ η` is induced by the monoidal functor `Ψ = - ⊗ᴸ_R S`. -/
theorem trace_localFrobenius_extendScalars (W : StrictWeilComplex (ModuleCat.{u + 1} R) g)
    (m : ℕ) (x : Spec (.of k) ⟶ X) (hx : x ≫ iterateHom g.hom m = x)
    [HasRightDual (L((x)^*[ModuleCat.{u + 1} R]).obj W.obj.obj)]
    [HasRightDual (L((x)^*[ModuleCat.{u + 1} S]).obj (W.extendScalars S aX).obj.obj)]
    [HasRightDual (L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).obj
      (L((x)^*[ModuleCat.{u + 1} R]).obj W.obj.obj))] :
    letI := leftDerivedSheafExtendScalarsMonoidal (R := R) (S := S) (Spec (.of k))
    trace ((W.extendScalars S aX).localFrobenius m x hx) =
      ε L(sheafExtendScalars (algebraMap R S) (Spec (.of k))) ≫
        L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).map
          (trace (W.localFrobenius m x hx)) ≫
        η L(sheafExtendScalars (algebraMap R S) (Spec (.of k))) := by
  let : HasRightDual ((L(sheafExtendScalars (algebraMap R S) X) ⋙
      L((x)^*[ModuleCat.{u + 1} S])).obj W.obj.obj) :=
    inferInstanceAs (HasRightDual (L((x)^*[ModuleCat.{u + 1} S]).obj
      (W.extendScalars S aX).obj.obj))
  let : HasRightDual ((L((x)^*[ModuleCat.{u + 1} R]) ⋙
      L(sheafExtendScalars (algebraMap R S) (Spec (.of k)))).obj W.obj.obj) :=
    inferInstanceAs (HasRightDual (L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).obj
      (L((x)^*[ModuleCat.{u + 1} R]).obj W.obj.obj)))
  rw [← trace_leftDerivedSheafExtendScalars_map]
  exact trace_eq_of_iso ((leftDerivedUpperStarExtendScalarsIso R S x).app W.obj.obj) _ _
    (localFrobenius_extendScalars (aX := aX) S W m x hx)

/-- **Coefficient change of the local traces, for scalar traces**: if
`tr_R(F_{x,m} ∣ K_x̄) = a • 𝟙`, then `tr_S(F_{x,m} ∣ (K_S)_x̄) = ρ a • 𝟙`. -/
theorem trace_localFrobenius_extendScalars_of_eq_smul
    (W : StrictWeilComplex (ModuleCat.{u + 1} R) g) (m : ℕ) (x : Spec (.of k) ⟶ X)
    (hx : x ≫ iterateHom g.hom m = x)
    [HasRightDual (L((x)^*[ModuleCat.{u + 1} R]).obj W.obj.obj)]
    [HasRightDual (L((x)^*[ModuleCat.{u + 1} S]).obj (W.extendScalars S aX).obj.obj)]
    [HasRightDual (L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).obj
      (L((x)^*[ModuleCat.{u + 1} R]).obj W.obj.obj))] {a : R}
    (ha : trace (W.localFrobenius m x hx) = a • 𝟙 _) :
    trace ((W.extendScalars S aX).localFrobenius m x hx) = algebraMap R S a • 𝟙 _ := by
  rw [trace_localFrobenius_extendScalars S W m x hx, ha]
  exact ε_comp_leftDerivedSheafExtendScalars_map_smul_id_comp_η _ a

end StrictWeilComplex

end AlgebraicGeometry.ProEtale
