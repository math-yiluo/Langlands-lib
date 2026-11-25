/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Sites.GaloisModule
public import WeilConjectures.FieldTheory.FiniteFieldGaloisCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.ForgetCohomologyVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension

/-!
# The cohomological dimension of a finite field

Let `k` be a finite field and `Λ` a ring in which a prime `ℓ` vanishes. Then
`H^q(Spec k, F) = 0` for every `q > 1` and every étale sheaf `F` of `Λ`-modules on `Spec k`; in
particular `Spec k` has finite cohomological dimension (blueprint
`lemma-cohomological-dimension-base-field`, in the sense of `definition-cohomological-dimension`,
i.e. `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimension`).

The cohomology of `F` is that of its underlying abelian sheaf (Stacks 03FD), which is the Galois
cohomology of its geometric fibre, an `ℓ`-primary discrete module over the absolute Galois group
`Gal(k̄/k)` (`AlgebraicGeometry.Scheme.sheafHAddEquivGaloisH`). This group has `ℓ`-cohomological
dimension one (`FiniteField.subsingleton_H_galois`), via its `ℓ`-adic procyclic quotient.

No assumption that `ℓ` is invertible in `k` is needed.

## Main statements

- `AlgebraicGeometry.Etale.isZero_cohomology_singleFunctor_iff_subsingleton_sheafH`: the
  cohomology of a sheaf of `Λ`-modules vanishes if and only if that of the underlying abelian
  sheaf does.
- `AlgebraicGeometry.Etale.isZero_cohomology_spec_of_finite`: the vanishing above degree one.
- `AlgebraicGeometry.Etale.hasFiniteCohomologicalDimension_of_finite`: the finiteness of the
  cohomological dimension.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

/-- In a discrete module, the endomorphism `n • 𝟙 M` acts as multiplication by `n`. -/
lemma DiscreteModule.nsmul_id_hom_apply {G : Type u} [Group G] [TopologicalSpace G]
    (M : DiscreteModule.{w} G) (n : ℕ) (x : M.obj.V) :
    (n • 𝟙 M).hom.hom.hom x = n • x := by
  have h : (ObjectProperty.ι _ ⋙ Action.forget AddCommGrpCat G).map (n • 𝟙 M) =
      n • (ObjectProperty.ι _ ⋙ Action.forget AddCommGrpCat G).map (𝟙 M) := by
    rw [Functor.map_nsmul]
  rw [CategoryTheory.Functor.map_id] at h
  have := congrArg (fun f ↦ f.hom x) h
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.comp_map, ObjectProperty.ι_map,
    Action.forget_map, AddCommGrpCat.hom_nsmul, AddCommGrpCat.hom_id, AddMonoidHom.smul_apply,
    AddMonoidHom.id_apply] at this
  exact this

/-- A discrete module `M` with `ℓ ^ j • 𝟙 M = 0` is `ℓ`-primary. -/
lemma DiscreteModule.isPrimary_of_pow_nsmul_id_eq_zero {G : Type u} [Group G]
    [TopologicalSpace G] {M : DiscreteModule.{w} G} {ℓ j : ℕ} (h : ℓ ^ j • 𝟙 M = 0) :
    DiscreteModule.IsPrimary ℓ M :=
  fun x ↦ ⟨j, by rw [← DiscreteModule.nsmul_id_hom_apply, h]; rfl⟩

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The cohomology of a sheaf of `Λ`-modules on `X_ét` vanishes in degree `q` if and only if the
cohomology of its underlying abelian sheaf does (Stacks 03FD). -/
theorem isZero_cohomology_singleFunctor_iff_subsingleton_sheafH (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) X q).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) ↔
      Subsingleton (Sheaf.H ((sheafForget₂ Λ X).obj G) q) := by
  obtain ⟨e⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso X Λ q
  obtain ⟨e'⟩ := Scheme.nonempty_sheafH_extDerivedIso X q
  refine ModuleCat.isZero_iff_subsingleton.trans ((AddCommGrpCat.isZero_iff_subsingleton
    (G := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj _)).symm.trans
    (Iff.trans ?_ (AddCommGrpCat.isZero_iff_subsingleton
      (G := (Sheaf.functorH X.smallEtaleTopology q).obj ((sheafForget₂ Λ X).obj G)))))
  exact ⟨fun h ↦ h.of_iso (e'.app _ ≪≫ (e.app G).symm),
    fun h ↦ h.of_iso (e.app G ≪≫ (e'.app _).symm)⟩

/-- Blueprint `lemma-cohomological-dimension-base-field`: the étale cohomology of the spectrum of a
finite field `k` vanishes above degree one, for sheaves of modules over a ring `Λ` killed by a prime
`ℓ`. The cohomology is the Galois cohomology of the geometric fibre, an `ℓ`-primary discrete module
over `Gal(k̄/k)` (`FiniteField.subsingleton_H_galois`). -/
theorem isZero_cohomology_spec_of_finite {k : Type u} [Field k] [Finite k] (ℓ : ℕ)
    [Fact ℓ.Prime] (hΛ : (ℓ : Λ) = 0)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) {q : ℕ} (hq : 1 < q) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) (Spec (.of k)) q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  rw [isZero_cohomology_singleFunctor_iff_subsingleton_sheafH]
  let Ω := AlgebraicClosure k
  have : (Scheme.etaleSheafEquivDiscreteModule k Ω).functor.Additive :=
    (Scheme.isGaloisPoint_galoisPoint k Ω).additive_equivalence_functor
  set A := (sheafForget₂ Λ (Spec (.of k))).obj F
  have hM : DiscreteModule.IsPrimary ℓ ((Scheme.etaleSheafEquivDiscreteModule k Ω).functor.obj A) :=
    DiscreteModule.isPrimary_of_pow_nsmul_id_eq_zero (j := 1) (by
      rw [pow_one, ← CategoryTheory.Functor.map_id, ← Functor.map_nsmul,
        ← CategoryTheory.Functor.map_id, ← Functor.map_nsmul,
        ← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul, Functor.map_zero, Functor.map_zero])
  have := FiniteField.subsingleton_H_galois ℓ _ hM hq
  exact (Scheme.sheafHAddEquivGaloisH k Ω A q).toEquiv.subsingleton

/-- Blueprint `lemma-cohomological-dimension-base-field`: the spectrum of a finite field has finite
étale cohomological dimension (`definition-cohomological-dimension`), namely at most one, for
sheaves of modules over a ring `Λ` killed by a prime `ℓ`. This covers in particular every finite
field `Λ` of characteristic `ℓ`; `ℓ` need not be invertible in `k`. -/
theorem hasFiniteCohomologicalDimension_of_finite {k : Type u} [Field k] [Finite k]
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : (ℓ : Λ) = 0) :
    HasFiniteCohomologicalDimension Λ (Spec (.of k)) := by
  refine ⟨1, fun F q hq ↦ ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by omega⟩
  exact isZero_cohomology_spec_of_finite ℓ hΛ F (by omega)

end AlgebraicGeometry.Etale
