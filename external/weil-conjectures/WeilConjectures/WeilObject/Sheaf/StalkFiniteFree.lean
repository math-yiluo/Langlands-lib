/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.TraceFormula.CategoricalTraceExact
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk

/-!

# Stalks of constructible `ℚ̄_ℓ`-sheaves at geometric points

Let `Ω` be a separably closed field, given as a commutative ring which is a field so that
`CommRingCat.of Ω` carries the ring structure of `Ω` itself, and let `Mod_{Spec Ω}` be the
category of `ℚ̲̄_ℓ`-modules on the pro-étale site of `Spec Ω`. The endomorphisms of its unit
form the field `ℚ̄_ℓ`
(`ProEtale.CondensedRing.isIso_of_ne_zero_end_tensorUnit`,
`ProEtale.CondensedRing.one_ne_zero_end_tensorUnit`), and the pullback of a homology sheaf of a
bounded constructible complex along a geometric point `x̄ : Spec Ω ⟶ X` is a finite free module,
a finite direct sum of copies of the unit
(`ProEtale.CondensedRing.isFiniteFree_upperStar_homology`).

The first two statements are transported, along the equivalence `p^*` from condensed
`ℚ̲̄_ℓ`-modules (`ProEtale.CondensedRing.isEquivalence_upperStarFromPointMod`, blueprint node
`proposition-pro-etale-site-separably-closed`), from the regular module `ℚ̲̄_ℓ`, whose
endomorphisms are the constants `ℚ̄_ℓ` (`Profinite.PadicAlgCl.isIso_of_ne_zero_end_regular`,
`Profinite.PadicAlgCl.one_ne_zero_end_regular`). The third combines the finite presentation of
the stalks of constructible module objects
(`ProEtale.CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject`) with the
rank normal form of morphisms between finite powers of the unit
(`CategoryTheory.Limits.exists_iso_biproduct_cokernel`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {Ω : Type u} [instΩ : CommRing Ω] (hΩ : IsField Ω)
  (hsep : letI := hΩ.toField; IsSepClosed Ω)

include hΩ hsep

/-- The endomorphisms of the unit of `Mod_{Spec Ω}` form a field: they are
`H⁰(Spec Ω, ℚ̲̄_ℓ) = ℚ̄_ℓ`, so every nonzero endomorphism of the unit is invertible. -/
theorem isIso_of_ne_zero_end_tensorUnit
    (t : End (𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω)))))) (ht : t ≠ 0) :
    IsIso t.asHom := by
  let := hΩ.toField
  have := isEquivalence_upperStarFromPointMod (Ω := Ω) (Profinite.padicAlgClRingObj ℓ)
  exact (upperStarFromPointMod _ _).isIso_of_ne_zero_end (Iso.refl _)
    (Profinite.PadicAlgCl.isIso_of_ne_zero_end_regular ℓ) t ht

/-- The unit of `Mod_{Spec Ω}` is not zero. -/
theorem one_ne_zero_end_tensorUnit :
    (1 : End (𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω)))))) ≠ 0 := by
  let := hΩ.toField
  have := isEquivalence_upperStarFromPointMod (Ω := Ω) (Profinite.padicAlgClRingObj ℓ)
  exact (upperStarFromPointMod _ _).one_ne_zero_end
    (X := Mod.regular (Profinite.padicAlgClRingObj ℓ)) (Iso.refl _)
    (Profinite.PadicAlgCl.one_ne_zero_end_regular ℓ)

/-- The pullback of a homology sheaf `Hʲ(K)` of a bounded constructible complex along a
geometric point `x̄ : Spec Ω ⟶ X` is finite free: its restriction to the stratum through `x̄` is
pro-étale locally finitely presented, every pro-étale cover of `Spec Ω` has a section, and a
finitely presented module over the field `ℚ̄_ℓ = End (𝟙_ Mod_{Spec Ω})` is free. -/
theorem isFiniteFree_upperStar_homology {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (j : ℤ) (x : Spec (.of Ω) ⟶ X.left) :
    letI := Abelian.hasFiniteBiproducts (C := CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))))
    IsFiniteFree ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
      ((DerivedCategory.homologyFunctor _ j).obj K.obj)) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := isFinitelyPresented_upperStar_of_isConstructibleModuleObject
    (Profinite.padicAlgClRingObj ℓ) hΩ hsep
    (((mem_boundedConstructible_iff _ _).1 K.property).2 j) x
  obtain ⟨k, ⟨e'⟩⟩ := Limits.exists_iso_biproduct_cokernel
    (isIso_of_ne_zero_end_tensorUnit ℓ hΩ hsep) (Iso.refl _) (Iso.refl _) f
  exact ⟨k, ⟨e ≪≫ e'⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
