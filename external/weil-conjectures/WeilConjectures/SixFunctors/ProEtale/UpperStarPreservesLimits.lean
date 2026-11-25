/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedPullbackLimitsAb
public import WeilConjectures.SixFunctors.ProEtale.UpperStarLimits.Affine

/-!
# The pullback of pro-étale sheaves preserves limits

For an arbitrary morphism of quasi-compact quasi-separated schemes `g : Z ⟶ Y`, the pullback
`g^*` of abelian pro-étale sheaves preserves all small limits
(`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_ab`); only the quasi-compactness and
quasi-separatedness of `Y` are used. The same holds for sheaves of modules
(`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_moduleCat`).

The objects `V = Spec A` of `Z_proét` with `A` w-contractible cover `Z_proét`. Over such a `V`
(say `Y = Spec R` affine), the factorizations `V ⟶ W ⟶ Y` through weakly étale `Y`-schemes `W`
have an initial one, `W₀ = Spec H_R(A)` with `H_R(A) = colim B` the colimit of the étale
`R`-algebras `B` mapping to `A` (`Algebra.ClosedLift R A`): every map to an ind-étale `R`-algebra
factors uniquely through it, and every weakly étale `R`-algebra becomes ind-étale after a
faithfully flat ind-étale cover, which splits over the w-contractible `A`. Hence the presheaf
pullback (the left Kan extension along base change) takes the value `F(W₀)` on `V`, and so does
its sheafification, `V` having disjoint refinements. The sections over `V` of `g^* F` are thus
`F(W₀)`, which commute with limits in `F`
(`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_of_isAffine_target`). For a general
quasi-compact quasi-separated `Y`, the restrictions to the preimages of a finite affine open
cover of `Y` jointly detect isomorphisms.

## References

- Bhatt–Scholze, *The pro-étale topology for schemes*, §2.2 and §4.2.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- **The pullback of pro-étale sheaves of modules preserves limits**: for a morphism
`g : Z ⟶ Y` to a quasi-compact quasi-separated scheme, the pullback `g^*` of pro-étale sheaves
of modules preserves all small limits. Over a finite affine open cover `Y = ⋃ Yₖ` this is
`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_of_isAffine_target`, and the
restrictions to the preimages `Z ×_Y Yₖ` jointly detect isomorphisms
(`AlgebraicGeometry.ProEtale.isIso_of_forall_isIso_upperStar_map`). -/
theorem preservesLimitsOfSize_upperStar_moduleCat {R : Type (u + 1)} [Ring R] {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] :
    PreservesLimitsOfSize.{u + 1, u + 1} ((g)^*[ModuleCat.{u + 1} R]) := by
  refine ⟨fun {J} _ ↦ ⟨fun {D} ↦ ?_⟩⟩
  let 𝒰 := Y.affineCover.finiteSubcover
  let o (k : 𝒰.I₀) := 𝒰.f k
  have hc (k : 𝒰.I₀) : IsIso ((pullback.fst g (o k))^*[ModuleCat.{u + 1} R].map
      (limit.post D (g)^*[ModuleCat.{u + 1} R])) := by
    have : PreservesLimitsOfSize.{u + 1, u + 1}
        ((pullback.snd g (o k))^*[ModuleCat.{u + 1} R]) :=
      preservesLimitsOfSize_upperStar_of_isAffine_target _
    have : PreservesLimitsOfSize.{u + 1, u + 1}
        ((pullback.fst g (o k))^*[ModuleCat.{u + 1} R]) :=
      preservesLimitsOfSize_upperStar_of_mono _
    have : PreservesLimitsOfSize.{u + 1, u + 1} ((o k)^*[ModuleCat.{u + 1} R]) :=
      preservesLimitsOfSize_upperStar_of_mono _
    have : PreservesLimitsOfSize.{u + 1, u + 1}
        ((pullback.snd g (o k) ≫ o k)^*[ModuleCat.{u + 1} R]) :=
      preservesLimitsOfSize_upperStar_comp _ _
    have : PreservesLimit D ((g)^*[ModuleCat.{u + 1} R] ⋙
        (pullback.fst g (o k))^*[ModuleCat.{u + 1} R]) :=
      preservesLimit_of_natIso D (eqToIso (congrArg (fun f ↦ (f)^*[ModuleCat.{u + 1} R])
        pullback.condition.symm) ≪≫ upperStarComp _ (pullback.fst g (o k)) g)
    have h := limit.post_post D (g)^*[ModuleCat.{u + 1} R]
      (pullback.fst g (o k))^*[ModuleCat.{u + 1} R]
    have : IsIso ((pullback.fst g (o k))^*[ModuleCat.{u + 1} R].map
        (limit.post D (g)^*[ModuleCat.{u + 1} R]) ≫
        limit.post (D ⋙ (g)^*[ModuleCat.{u + 1} R])
          (pullback.fst g (o k))^*[ModuleCat.{u + 1} R]) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (limit.post (D ⋙ (g)^*[ModuleCat.{u + 1} R])
      (pullback.fst g (o k))^*[ModuleCat.{u + 1} R])
  have : IsIso (limit.post D (g)^*[ModuleCat.{u + 1} R]) :=
    isIso_of_forall_isIso_upperStar_map (fun k ↦ pullback.fst g (o k)) (fun z ↦ by
      obtain ⟨y, hy⟩ := 𝒰.covers (g.base z)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback z y hy.symm
      exact ⟨𝒰.idx (g.base z), w, hw⟩) _ hc
  exact preservesLimit_of_isIso_post _ _

/-- **The pullback of pro-étale sheaves preserves limits**: for a morphism `g : Z ⟶ Y` of
quasi-compact quasi-separated schemes, the pullback `g^*` of abelian pro-étale sheaves preserves
all small limits. (Only the quasi-compactness and quasi-separatedness of `Y` are used, see
`AlgebraicGeometry.ProEtale.preservesLimitsOfSize_upperStar_moduleCat`.) -/
theorem preservesLimitsOfSize_upperStar_ab {Z Y : Scheme.{u}} (g : Z ⟶ Y) [CompactSpace Z]
    [QuasiSeparatedSpace Z] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    PreservesLimitsOfSize.{u + 1, u + 1} ((g)^*[Ab.{u + 1}]) :=
  have := preservesLimitsOfSize_upperStar_moduleCat (R := ULift.{u + 1} ℤ) g
  preservesLimitsOfSize_upperStar_ab_of_moduleCat g

end AlgebraicGeometry.ProEtale
