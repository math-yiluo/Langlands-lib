/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Reductions and limits of sheaves of continuous functions

Let `X` be a scheme and `R` a topological commutative ring, for instance the ring of integers
`𝒪_E` of a finite extension `E` of `ℚ_ℓ`. The abelian sheaf `U ↦ C(U, R)` on `X_proét`
(`AlgebraicGeometry.ProEtale.continuousMapAbSheaf`) behaves like the `ℓ`-adic integral sheaf
`𝒪_{E,X}` of Bhatt–Scholze (*The pro-étale topology for schemes*, §6.8):

- `AlgebraicGeometry.ProEtale.shortExact_continuousMapReductionShortComplex`: if multiplication
  by `a ∈ R` is an embedding and `π : R →+* Q` is a continuous surjection onto a discrete ring
  with kernel `a R`, then `0 ⟶ C(-, R) --a--> C(-, R) --π--> C(-, Q) ⟶ 0` is short exact;
  for `R = 𝒪_E`, `a = ℓⁿ` this computes `𝒪_{E,X} / ℓⁿ` as `C(-, 𝒪_E ⧸ ℓⁿ)`, which is `ν^*` of a
  constant étale sheaf
  (`AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafIsoContinuousMapRingSheaf`);
- `AlgebraicGeometry.ProEtale.isLimitContinuousMapAbSheafCone`: if `R` is the limit of a tower of
  topological rings `Qₙ`, then `C(-, R)` is the limit of the sheaves `C(-, Qₙ)`; for
  `R = 𝒪_E`, `Qₙ = 𝒪_E ⧸ ℓⁿ` this is `𝒪_{E,X} = lim 𝒪_{E,X} / ℓⁿ`.

These are the underived parts of step (3) of the comparison of `ℓ`-adic sheaves with `ℓ`-adic
towers of torsion étale sheaves needed for the finiteness theorem
(`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`).
-/

@[expose] public section
universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) {R Q : Type} [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]
  [TopologicalSpace Q] [Ring Q] [IsTopologicalRing Q]

/-- The abelian sheaf `U ↦ C(U, R)` underlying the sheaf of rings of continuous maps to a
topological ring `R`. -/
noncomputable abbrev continuousMapAbSheaf (R : Type) [TopologicalSpace R] [Ring R]
    [IsTopologicalRing R] : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (continuousMapRingSheaf X R)

variable (R) in
/-- Multiplication by an element `a` of a topological commutative ring `R`, as an endomorphism of
the abelian sheaf `U ↦ C(U, R)`. -/
noncomputable def continuousMapAbSheafMul (a : R) :
    continuousMapAbSheaf X R ⟶ continuousMapAbSheaf X R where
  hom :=
    { app U := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((AddMonoidHom.mulLeft (ContinuousMap.const U.unop.left a)).comp
          AddEquiv.ulift.toAddMonoidHom))
      naturality _ _ _ := rfl }

/-- Postcomposition with a continuous ring homomorphism `π : R →+* Q`, as a morphism of the
abelian sheaves of continuous maps. -/
noncomputable abbrev continuousMapAbSheafMap {T T' : Type} [TopologicalSpace T] [Ring T]
    [IsTopologicalRing T] [TopologicalSpace T'] [Ring T'] [IsTopologicalRing T'] (π : T →+* T')
    (hπ : Continuous π) : continuousMapAbSheaf X T ⟶ continuousMapAbSheaf X T' :=
  (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap X π hπ)

/-- The short complex `C(-, R) --a--> C(-, R) --π--> C(-, Q)` of abelian sheaves. -/
noncomputable def continuousMapReductionShortComplex (a : R) (π : R →+* Q) (hπ : Continuous π)
    (ha : π a = 0) : ShortComplex (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  ShortComplex.mk (continuousMapAbSheafMul X R a) (continuousMapAbSheafMap X π hπ) (by
    ext U f
    refine congrArg ULift.up (ContinuousMap.ext fun x ↦ ?_)
    change π (a * _) = 0
    rw [map_mul, ha, zero_mul])

variable [DiscreteTopology Q]

/-- Postcomposition with a surjective continuous ring homomorphism onto a discrete ring is an
epimorphism of abelian sheaves of continuous maps: it is surjective on sections, a continuous map
to a discrete space lifting along any set-theoretic section. -/
lemma epi_continuousMapAbSheafMap {T : Type} [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
    (π : T →+* Q) (hπ : Continuous π) (hsurj : Function.Surjective π) :
    Epi (continuousMapAbSheafMap X π hπ) := by
  have (U : X.ProEtᵒᵖ) : Epi (((sheafToPresheaf _ _).map
      (continuousMapAbSheafMap X π hπ)).app U) := by
    refine (AddCommGrpCat.epi_iff_surjective _).2 fun q ↦ ?_
    refine ⟨ULift.up ⟨Function.surjInv hsurj ∘ q.down,
      continuous_of_discreteTopology.comp q.down.continuous⟩, ?_⟩
    exact congrArg ULift.up (ContinuousMap.ext fun x ↦ Function.surjInv_eq hsurj _)
  exact (sheafToPresheaf _ _).epi_of_epi_map (NatTrans.epi_of_epi_app _)

/-- **Reduction of continuous functions**: let `R` be a topological commutative ring, `a ∈ R`
such that multiplication by `a` is an embedding, and `π : R →+* Q` a continuous surjection onto
a discrete ring with kernel `a R`. Then `0 ⟶ C(-, R) --a--> C(-, R) --π--> C(-, Q) ⟶ 0` is a
short exact sequence of abelian sheaves on `X_proét`. It is even exact on sections: a continuous
map to `a R` is `a` times a continuous map, multiplication by `a` being an embedding, and a
continuous map to the discrete `Q` lifts along any set-theoretic section of `π`. -/
theorem shortExact_continuousMapReductionShortComplex (a : R) (π : R →+* Q) (hπ : Continuous π)
    (ha : π a = 0) (hsurj : Function.Surjective π) (hker : ∀ x, π x = 0 → ∃ y, a * y = x)
    (hemb : Topology.IsEmbedding (a * · : R → R)) :
    (continuousMapReductionShortComplex X a π hπ ha).ShortExact where
  exact := by
    refine ShortComplex.exact_of_exact_sectionsFunctor _ _ fun W ↦ ?_
    rw [ShortComplex.ab_exact_iff]
    intro f hf
    have hf' (x) : π (f.down x) = 0 := congrArg (fun g : ULift.{u + 1} C(_, Q) ↦ g.down x) hf
    choose y hy using fun x ↦ hker _ (hf' x)
    have hcont : Continuous y := hemb.continuous_iff.2 (by
      convert f.down.continuous using 1
      exact funext hy)
    exact ⟨ULift.up ⟨y, hcont⟩, congrArg ULift.up (ContinuousMap.ext hy)⟩
  mono_f := by
    have (U : X.ProEtᵒᵖ) : Mono (((sheafToPresheaf _ _).map
        (continuousMapReductionShortComplex X a π hπ ha).f).app U) := by
      refine (AddCommGrpCat.mono_iff_injective _).2 fun f g h ↦ ?_
      refine congrArg ULift.up (ContinuousMap.ext fun x ↦ hemb.injective ?_)
      exact congrArg (fun k : ULift.{u + 1} C(_, R) ↦ k.down x) h
    exact (sheafToPresheaf _ _).mono_of_mono_map (NatTrans.mono_of_mono_app _)
  epi_g := epi_continuousMapAbSheafMap X π hπ hsurj

section Limit

variable {Qs : ℕ → Type} [∀ n, TopologicalSpace (Qs n)] [∀ n, Ring (Qs n)]
  [∀ n, IsTopologicalRing (Qs n)] (τ : ∀ n, Qs (n + 1) →+* Qs n) (hτ : ∀ n, Continuous (τ n))
  (π : ∀ n, R →+* Qs n) (hπ : ∀ n, Continuous (π n)) (hπτ : ∀ n, (τ n).comp (π (n + 1)) = π n)

/-- The tower `n ↦ C(-, Qₙ)` of abelian sheaves attached to a tower of topological rings. -/
noncomputable def continuousMapAbSheafTower : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  Functor.ofOpSequence (C := Sheaf (ProEt.topology X) Ab.{u + 1})
    (X := fun n ↦ continuousMapAbSheaf X (Qs n))
    fun n ↦ continuousMapAbSheafMap X (τ n) (hτ n)

lemma continuousMapAbSheafTower_map_succ (n : ℕ) :
    (continuousMapAbSheafTower X τ hτ).map (homOfLE (n.le_add_right 1)).op =
      continuousMapAbSheafMap X (τ n) (hτ n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The cone `C(-, R) ⟶ C(-, Qₙ)` over the tower `n ↦ C(-, Qₙ)`, for compatible continuous ring
homomorphisms `πₙ : R →+* Qₙ`. -/
noncomputable def continuousMapAbSheafCone : Cone (continuousMapAbSheafTower X τ hτ) where
  pt := continuousMapAbSheaf X R
  π := NatTrans.ofOpSequence (fun n ↦ continuousMapAbSheafMap X (π n) (hπ n)) fun n ↦ by
    refine (Category.id_comp _).trans ?_
    erw [continuousMapAbSheafTower_map_succ]
    ext U f
    exact congrArg ULift.up (ContinuousMap.ext fun x ↦ (RingHom.congr_fun (hπτ n) _).symm)

/-- **Continuous functions to a limit of topological rings**: if `R` is the limit of the tower of
topological rings `Qₙ`, i.e. the maps `πₙ : R → Qₙ` are jointly injective, every compatible
family comes from `R`, and `R` carries the topology induced by the `πₙ`, then the abelian sheaf
`U ↦ C(U, R)` is the limit of the sheaves `U ↦ C(U, Qₙ)`. This holds sectionwise: a compatible
family of continuous maps `U → Qₙ` glues to a map `U → R`, continuous since `R` carries the
induced topology. -/
noncomputable def isLimitContinuousMapAbSheafCone
    (hinj : ∀ x y : R, (∀ n, π n x = π n y) → x = y)
    (hsurj : ∀ q : ∀ n, Qs n, (∀ n, τ n (q (n + 1)) = q n) → ∃ x, ∀ n, π n x = q n)
    (hind : Topology.IsInducing (fun x n ↦ π n x : R → ∀ n, Qs n)) :
    IsLimit (continuousMapAbSheafCone X τ hτ π hπ hπτ) := by
  have : ReflectsLimitsOfShape ℕᵒᵖ (forget Ab.{u + 1}) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  refine isLimitOfReflects (sheafToPresheaf _ _) (evaluationJointlyReflectsLimits _ fun U ↦
    isLimitOfReflects (forget Ab.{u + 1}) ((Types.isLimit_iff _).2 fun s hs ↦ ?_).some)
  have hcompat (y : U.unop.left) (n : ℕ) :
      τ n ((s (op (n + 1))).down y) = (s (op n)).down y := by
    have h := hs (homOfLE (n.le_add_right 1)).op
    simp only [Functor.comp_map] at h
    erw [continuousMapAbSheafTower_map_succ] at h
    exact congrArg (fun g : ULift.{u + 1} C(U.unop.left, Qs n) ↦ g.down y) h
  choose x hx using fun y ↦ hsurj (fun n ↦ (s (op n)).down y) (hcompat y)
  have hcont : Continuous x := hind.continuous_iff.2 (continuous_pi fun n ↦ by
    convert (s (op n)).down.continuous using 1
    exact funext fun y ↦ hx y n)
  refine ⟨ULift.up ⟨x, hcont⟩, fun j ↦ ?_, fun z hz ↦ ?_⟩
  · exact congrArg ULift.up (ContinuousMap.ext fun y ↦ hx y j.unop)
  · refine congrArg ULift.up (ContinuousMap.ext fun y ↦ hinj _ _ fun n ↦ ?_)
    refine (congrArg (fun g : ULift.{u + 1} C(U.unop.left, Qs n) ↦ g.down y) (hz (op n))).trans ?_
    exact (hx y n).symm

end Limit

end AlgebraicGeometry.ProEtale
