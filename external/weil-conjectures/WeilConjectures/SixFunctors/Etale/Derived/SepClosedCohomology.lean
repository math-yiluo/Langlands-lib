/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Sites.LocalSite
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

/-!
# Étale cohomology of the spectrum of a separably closed field

Let `K` be a separably closed field and `s = Spec K`. Every covering sieve of the terminal
object of the small étale site of `s` is trivial, so this site is a local site, and the
constant sheaf functor is fully faithful: the global sections of the constant sheaf `Λ` are
`Λ`. The global sections functor is exact on étale sheaves of `Λ`-modules on `s`, so the
étale cohomology of a sheaf `F` on `s` is `Γ(s, F)` in degree `0` and vanishes in the other
degrees.

## Main definitions and results

- `AlgebraicGeometry.Scheme.isLocalSite_smallEtaleTopology_of_isSepClosed_derived`: the small étale
  site of `Spec K` is a local site.
- `AlgebraicGeometry.Scheme.globalSectionsUnitIsoOfIsSepClosed`: `Γ(Spec K, Λ) ≅ Λ`.
- `AlgebraicGeometry.Etale.cohomology_singleFunctor_of_isSepClosed`: `H^0(Spec K, F) ≅ Γ(F)`
  and `H^q(Spec K, F) = 0` for `q ≠ 0`.
- `AlgebraicGeometry.HasInvertibleExponent.spec_of_charP`: a finite ring `Λ` in which the
  characteristic `p` of a field `Ω` is invertible has invertible exponent on `Spec Ω`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

/-- Let `Λ` be a finite ring in which the characteristic `p` of a field `Ω` is invertible.
Then the exponent of `Λ`, its characteristic, is invertible on `Spec Ω`: if `p` divided the
characteristic `n = p m` of `Λ`, then `m` would vanish in `Λ`, so `n ∣ m` and `p = 1`. -/
theorem HasInvertibleExponent.spec_of_charP (Λ : Type*) [CommRing Λ] [Finite Λ]
    {Ω : Type u} [Field Ω] (p : ℕ) [CharP Ω p] [Invertible (p : Λ)] :
    HasInvertibleExponent Λ (Spec (.of Ω)) := by
  have hn : ringChar Λ ≠ 0 := CharP.char_ne_zero_of_finite Λ _
  refine ⟨ringChar Λ, Nat.pos_of_ne_zero hn, ringChar.Nat.cast_ringChar, ?_⟩
  have h : (ringChar Λ : Ω) ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := (CharP.cast_eq_zero_iff Ω p _).1 h
    have hm0 : (m : Λ) = 0 := by
      have h' : (p : Λ) * m = 0 := by rw [← Nat.cast_mul, ← hm, ringChar.Nat.cast_ringChar]
      simpa using congrArg (⅟(p : Λ) * ·) h'
    have hmn : m = ringChar Λ :=
      Nat.dvd_antisymm (Dvd.intro_left p hm.symm) ((ringChar.spec Λ m).1 hm0)
    rw [hmn] at hm
    exact CharP.ringChar_ne_one (ringChar.eq Ω p ▸ (Nat.mul_eq_right hn).1 hm.symm)
  simpa using (IsUnit.mk0 _ h).map (Scheme.ΓSpecIso (.of Ω)).inv.hom

namespace Scheme

open CategoryTheory.GrothendieckTopology

variable (K : Type u) [Field K] [IsSepClosed K]

/-- Over a separably closed field `K`, the small étale site of `Spec K` is a local site: every
covering sieve of its terminal object contains the identity
(`AlgebraicGeometry.Scheme.id_mem_of_mem_smallEtaleTopology_of_isSepClosed`). -/
instance isLocalSite_smallEtaleTopology_of_isSepClosed_derived :
    (Spec (.of K)).smallEtaleTopology.IsLocalSite where
  eq_top_of_mem S hS := by
    let e : etalePoint K ≅ ⊤_ _ := isTerminalEtalePoint.uniqueUpToIso terminalIsTerminal
    have h := id_mem_of_mem_smallEtaleTopology_of_isSepClosed K (S.pullback e.hom)
      ((Spec (.of K)).smallEtaleTopology.pullback_stable e.hom hS)
    rw [Sieve.pullback_apply, Category.id_comp] at h
    rw [← Sieve.id_mem_iff_eq_top]
    simpa using S.downward_closed h e.inv

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Over a separably closed field `K`, the global sections functor on étale sheaves of
`Λ`-modules on `Spec K` preserves epimorphisms. -/
instance preservesEpimorphisms_Γ_of_isSepClosed :
    (Sheaf.Γ (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).PreservesEpimorphisms :=
  Functor.PreservesEpimorphisms.of_iso
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).symm

/-- Over a separably closed field `K`, the global sections functor on étale sheaves of
`Λ`-modules on `Spec K` is exact; in particular it preserves finite colimits. -/
instance preservesFiniteColimits_Γ_of_isSepClosed :
    PreservesFiniteColimits (Sheaf.Γ (Spec (.of K)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) :=
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    (Sheaf.Γ (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
  Functor.preservesFiniteColimits_of_preservesHomology _

variable {Λ} in
/-- Over a separably closed field `K`, the global sections of the constant sheaf `Λ`, the
monoidal unit, on the small étale site of `Spec K` are `Λ`: the constant sheaf functor of a
local site is fully faithful. -/
def globalSectionsUnitIsoOfIsSepClosed (Λ : Type (u + 1)) [CommRing Λ] :
    (Sheaf.Γ (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (𝟙_ _) ≅
      ModuleCat.of Λ Λ :=
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  (Sheaf.Γ _ _).mapIso (Functor.Monoidal.εIso (presheafToSheaf _ _)) ≪≫
    (asIso ((constantSheafΓAdj (Spec (.of K)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).unit.app (ModuleCat.of Λ Λ))).symm

end Scheme

namespace Etale

open Scheme

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- The derived global sections `RΓ(X, -)` are an additive functor, being triangulated. -/
instance additive_rightDerivedGlobalSections (X : Scheme.{u}) :
    (rightDerivedGlobalSections A X).Additive :=
  inferInstanceAs ((Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor.Additive)

variable (K : Type u) [Field K] [IsSepClosed K] (Λ : Type (u + 1)) [CommRing Λ]

/-- **Cohomology of a separably closed point.** For an étale sheaf `F` of `Λ`-modules on
`Spec K`, `K` separably closed, `H^0(Spec K, F) ≅ Γ(Spec K, F)` and `H^q(Spec K, F) = 0` for
`q ≠ 0`: the global sections functor is exact, so its right derived functor is computed
termwise. -/
theorem cohomology_singleFunctor_of_isSepClosed
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((cohomology (ModuleCat.{u + 1} Λ) (Spec (.of K)) 0).obj
        ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (Sheaf.Γ (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj F) ∧
      ∀ q : ℤ, q ≠ 0 → IsZero ((cohomology (ModuleCat.{u + 1} Λ) (Spec (.of K)) q).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  let e (q : ℤ) := ((Sheaf.Γ (Spec (.of K)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).rightDerivedFunctorHomologyFunctorIso q).symm.app
      ((DerivedCategory.singleFunctor _ 0).obj F)
  refine ⟨⟨e 0 ≪≫ (Sheaf.Γ _ _).mapIso
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F)⟩, fun q hq ↦ ?_⟩
  refine IsZero.of_iso ((Sheaf.Γ _ _).map_isZero ?_) (e q)
  rcases lt_or_gt_of_ne hq with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 q h
  · exact DerivedCategory.isZero_of_isLE _ 0 q h

end Etale

end AlgebraicGeometry
