/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity

/-!
# Constant sheaves and the comparison pullback

Let `X` be a scheme and `ν : X_ét ⥤ X_proét` the inclusion of the small étale site into the
small pro-étale site. This file proves:

- `AlgebraicGeometry.ProEtale.constantSheafCompComparisonUpperStarIso`: the comparison pullback
  `ν^*` of a constant étale sheaf is the constant pro-étale sheaf, both functors being left
  adjoint to global sections;
- `AlgebraicGeometry.ProEtale.constantSheafIsoContinuousMapRingSheaf`: for a discrete topological
  ring `T`, the abelian sheaf `U ↦ C(U, T)` on `X_proét` is the constant sheaf with value `T`
  (Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 4.2.12): a continuous map to a
  discrete space is locally constant;
- `AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafIsoContinuousMapRingSheaf`: hence
  `U ↦ C(U, T)` is `ν^*` of the constant étale sheaf with value `T`.

For `T = 𝒪_E ⧸ ℓⁿ` this identifies the reductions of the sheaf `𝒪_{E,X}` of continuous
`𝒪_E`-valued functions (`WeilConjectures.SixFunctors.ProEtale.Adic.ContinuousMapReduction`) with
pullbacks of constant torsion étale sheaves, an input of the comparison of `ℓ`-adic sheaves with
`ℓ`-adic towers of torsion étale sheaves needed for the finiteness theorem
(`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`).
-/

@[expose] public section
universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

section Comparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (X : Scheme.{u})

/-- The comparison pullback of a constant étale sheaf is the constant pro-étale sheaf: both
`ν^*` composed with the constant sheaf functor and the constant sheaf functor are left adjoint to
the global sections functor, as `Γ(X_ét, ν_* -) ≅ Γ(X_proét, -)`
(`AlgebraicGeometry.ProEtale.comparisonLowerStarCompGlobalSectionsIso`). -/
noncomputable def constantSheafCompComparisonUpperStarIso :
    constantSheaf X.smallEtaleTopology A ⋙ ν^*(X)[A] ≅ constantSheaf (ProEt.topology X) A :=
  (((constantSheafΓAdj _ A).comp (comparisonAdjunction A X)).ofNatIsoRight
    (comparisonLowerStarCompGlobalSectionsIso A X)).leftAdjointUniq (constantSheafΓAdj _ A)

end Comparison

section Discrete

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- The constant functions, as a morphism from the constant abelian presheaf with value `T` to
the presheaf `U ↦ C(U, T)`. -/
noncomputable def constToContinuousMapPresheaf :
    (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} T)) ⟶
      continuousMapRingPresheaf X T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1} where
  app _ := AddCommGrpCat.ofHom
    { toFun t := ULift.up (ContinuousMap.const _ t.down)
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

variable [DiscreteTopology T]

/-- The constant functions are locally bijective onto the continuous maps to a discrete ring: a
continuous map to a discrete space is constant on the open fibres, and two constants agreeing as
functions on a nonempty space are equal. -/
lemma w_constToContinuousMapPresheaf :
    (ProEt.topology X).W (constToContinuousMapPresheaf X T) := by
  rw [GrothendieckTopology.W_iff_isLocallyBijective]
  refine ⟨⟨fun {U} x y h ↦ ProEt.mem_topology_of_isOpenImmersion U.unop _
    (fun _ : U.unop.left ↦ overOpens (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U.unop ⊤)
    (fun _ ↦ overOpensι (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U.unop ⊤)
    (fun _ ↦ inferInstanceAs (IsOpenImmersion (⊤ : U.unop.left.Opens).ι))
    (fun p ↦ ⟨p, ⟨p, trivial⟩, rfl⟩) fun p ↦ ?_⟩, ⟨fun {U} s ↦ ?_⟩⟩
  · have hxy : x = y := by
      obtain ⟨x⟩ := x
      obtain ⟨y⟩ := y
      have := congrArg (fun z : ULift.{u + 1} C(U.unop.left, T) ↦ z.down p) h
      exact congrArg ULift.up this
    subst hxy
    rfl
  · refine ProEt.mem_topology_of_isOpenImmersion U _
      (fun p : U.left ↦ overOpens (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U
        ⟨s.down ⁻¹' {s.down p}, (isOpen_discrete _).preimage s.down.continuous⟩)
      (fun p ↦ overOpensι (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U _)
      (fun p ↦ inferInstanceAs (IsOpenImmersion (Opens.ι _)))
      (fun p ↦ ⟨p, ⟨p, rfl⟩, rfl⟩) fun p ↦ ⟨ULift.up (s.down p), ?_⟩
    refine congrArg ULift.up (ContinuousMap.ext fun q ↦ ?_)
    exact q.2.symm

/-- **Continuous maps to a discrete ring form the constant sheaf** (Bhatt–Scholze,
Lemma 4.2.12): for a discrete topological ring `T`, the abelian sheaf `U ↦ C(U, T)` on the
pro-étale site of `X` is the constant sheaf with value `T`. A continuous map to a discrete space
is locally constant, so the constant functions are locally surjective onto it. -/
noncomputable def constantSheafIsoContinuousMapRingSheaf :
    (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} T)) ≅
      (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X T) :=
  have := ((ProEt.topology X).W_iff _).1 (w_constToContinuousMapPresheaf X T)
  asIso ((presheafToSheaf _ _).map (constToContinuousMapPresheaf X T)) ≪≫
    asIso ((sheafificationAdjunction _ _).counit.app ((sheafCompose (ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)))

/-- The abelian sheaf `U ↦ C(U, T)` of continuous maps to a discrete ring `T` is the comparison
pullback `ν^*` of the constant étale sheaf with value `T`. -/
noncomputable def comparisonUpperStarConstantSheafIsoContinuousMapRingSheaf :
    ν^*(X)[Ab.{u + 1}].obj ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} T))) ≅
      (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X T) :=
  (constantSheafCompComparisonUpperStarIso Ab.{u + 1} X).app _ ≪≫
    constantSheafIsoContinuousMapRingSheaf X T

end Discrete

end AlgebraicGeometry.ProEtale
