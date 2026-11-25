/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.ModuleCohomologyExt
public import WeilConjectures.SixFunctors.Etale.ForgetModuleCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit

/-!
# Étale cohomology classes with coefficients in a ring are abelian cohomology classes

Let `X` be a quasi-compact quasi-separated scheme and `Λ` a ring. The cohomology classes of the
constant sheaf `Λ_X` used in the duality theory, morphisms `Λ_X ⟶ Λ_X[n]` in `D(X_ét, Λ)`, are
the classes of the abelian cohomology `Hⁿ(X_ét, Λ)` of the underlying abelian sheaf
(`AlgebraicGeometry.Etale.unitShiftAddEquivH`): `Ext^n(Λ_X, Y)` computed with sheaves of
`Λ`-modules is `Hⁿ(X_ét, Y)` (`AlgebraicGeometry.Etale.bijective_mapExtComp_constantIntToRing`),
by dimension shifting, injective sheaves of `Λ`-modules being acyclic as abelian sheaves
(`CategoryTheory.Sheaf.subsingleton_H_succ_forget₂_of_injective`). No flatness of `Λ` over `ℤ`
is needed, so this applies to `Λ = ℤ/ℓᵐ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian MonoidalCategory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The terminal object `X` of the small étale site of `X`. -/
noncomputable abbrev terminalEtale : X.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)

/-- The terminal object of the small étale site. -/
noncomputable def terminalEtaleIsTerminal : IsTerminal (terminalEtale X) :=
  MorphismProperty.Over.mkIdTerminal _ X

/-- On a quasi-compact quasi-separated scheme, the underlying abelian sheaf of an injective étale
sheaf of `Λ`-modules has no higher cohomology. -/
theorem subsingleton_H_succ_sheafForget₂_obj_of_injective [CompactSpace X]
    [QuasiSeparatedSpace X] (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I]
    (q : ℕ) : Subsingleton (Sheaf.H ((sheafForget₂ Λ X).obj I) (q + 1)) := by
  let B : X.Etale → Prop := fun W ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left
  have hcov (V : X.Etale) (hV : B V) (R : Sieve V) (hR : R ∈ X.smallEtaleTopology V) :
      ∃ (n : ℕ) (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) ∧
        (∀ a, R (U a).hom) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ X.smallEtaleTopology V := by
    obtain ⟨_, _⟩ := hV
    obtain ⟨n, U, g, hRg, hU, hg⟩ := Scheme.exists_finite_affine_of_mem_smallEtaleTopology hR
    refine ⟨n, fun a ↦ Over.mk (g a), fun k y ↦ ?_, hRg,
      (Scheme.ofArrows_mem_smallEtaleTopology_iff g).2 hg⟩
    refine Scheme.compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦ ?_
    have := hU (y l)
    exact ⟨inferInstanceAs (CompactSpace (U (y l)).left),
      inferInstanceAs (QuasiSeparatedSpace (U (y l)).left)⟩
  exact Sheaf.subsingleton_H_succ_forget₂_of_injective (terminalEtaleIsTerminal X) B
    ⟨‹CompactSpace X›, ‹QuasiSeparatedSpace X›⟩ hcov I q

/-- **`Ext` over `Λ` is abelian cohomology.** On a quasi-compact quasi-separated scheme, for
every étale sheaf `Y` of `Λ`-modules, `e ↦ u ∘ e`, `Ext^n(Λ_X, Y) ⟶ Hⁿ(X_ét, Y)`, is bijective,
where `u : ℤ_X ⟶ Λ_X` is the class of `1`. -/
theorem bijective_mapExtComp_constantIntToRing [CompactSpace X] [QuasiSeparatedSpace X]
    (Y : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    Function.Bijective ((sheafForget₂ Λ X).mapExtComp
      (Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ) Y n) := by
  refine (sheafForget₂ Λ X).bijective_mapExtComp _ (fun Y ↦ ?_)
    (fun I _ q ↦ subsingleton_H_succ_sheafForget₂_obj_of_injective Λ X I q) Y n
  have hcomp : ((sheafForget₂ Λ X).mapExtComp
      (Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ) Y 0) ∘
        Ext.mk₀ = Ext.mk₀ ∘ fun f ↦
          Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ ≫
            (sheafForget₂ Λ X).map f := by
    funext f
    rw [Function.comp_apply, Functor.mapExtComp_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
    rfl
  have hb := (Ext.mk₀_bijective _ _).comp
    (Sheaf.bijective_comp_forget₂_map X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ Y)
  rw [← hcomp] at hb
  exact (Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective _ _)).1 hb

/-- **Classes in `D(X_ét, Λ)` are abelian cohomology classes.** On a quasi-compact
quasi-separated scheme, `Hom(Λ_X, Λ_X[n])` in `D(X_ét, Λ)` is the abelian cohomology group
`Hⁿ(X_ét, Λ)` of the underlying abelian sheaf of `Λ_X`. -/
noncomputable def unitShiftAddEquivH [CompactSpace X] [QuasiSeparatedSpace X] (n : ℕ) :
    (𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦(n : ℤ)⟧) ≃+
      Sheaf.H ((sheafForget₂ Λ X).obj
        (Sheaf.constantRing X.smallEtaleTopology Λ)) n :=
  let e := unitIsoSingleFunctorConstantSheaf Λ X
  (AddEquiv.mk' (e.homCongr ((shiftFunctor _ (n : ℤ)).mapIso e)) fun f g ↦ by
      simp [Iso.homCongr_apply]).trans <|
    (Ext.homAddEquiv (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).symm.trans <|
      AddEquiv.ofBijective _ (bijective_mapExtComp_constantIntToRing Λ X _ n)

end AlgebraicGeometry.Etale
