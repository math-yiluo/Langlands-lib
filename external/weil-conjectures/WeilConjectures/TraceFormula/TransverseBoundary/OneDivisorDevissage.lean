/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularOpens
public import WeilConjectures.ConstructibleSheaf.DistTriang
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerivedUnbounded
public import WeilConjectures.TraceFormula.TransverseBoundary.MonodromyDevissage
public import WeilConjectures.TraceFormula.TransverseBoundary.MonodromyPullback

/-!
# Local constancy of a direct image by dévissage

Let `j : V ⟶ W` be an open immersion into a locally noetherian regular scheme and `ι : D ⟶ W` a
morphism (in the application, the inclusion of a divisor in the complement of `V`). If, for every
finite `Λ`-module `N` killed by `ℓ`, the complex `ι^* Rj_* N_V` has finite locally constant
cohomology sheaves, then so has `ι^* Rj_* E` for every bounded complex `E` on `V` whose cohomology
sheaves have finite `ℓ`-group monodromy (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`,
*Complexes*).

The question is local on `D`; over a connected component `Q` of `W`, which is irreducible since
`W` is regular, `V ∩ Q` is irreducible or empty, and the dévissage of sheaves with finite
`ℓ`-group monodromy on the connected scheme `V ∩ Q`
(`AlgebraicGeometry.Etale.prop_of_isBoundedFiniteEllGroupMonodromy`) reduces the assertion to the
constant sheaves, using étale base change along `Q ⟶ W`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarRightDerivedLowerStarIsoOfEtale`) and the stability
of finite local constancy of cohomology under shifts and extensions
(`AlgebraicGeometry.Scheme.HasFiniteLocallyConstantHomology.of_distTriang`).

## Main statements

- `AlgebraicGeometry.Etale.hasFiniteLocallyConstantHomology_of_constantSheaf`
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
  (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)

/-- The restriction along `O = ι⁻¹(Q) ⟶ D` of `ι^* Rj_* K` is `ι_Q^* R j_{Q*} (K|_{V ∩ Q})` for an
open `Q` of `W`: étale base change along `Q ⟶ W`. -/
noncomputable def restrictOpensIso {W V D : Scheme.{u}} (j : V ⟶ W) (ι : D ⟶ W) (Q : W.Opens)
    (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ)
    [K.IsGE a] :
    (L((ι ∣_ Q)^*[ModuleCat.{u + 1} Λ])).obj ((R((j ∣_ Q)_*[ModuleCat.{u + 1} Λ])).obj
        ((L(((j ⁻¹ᵁ Q).ι)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (L(((ι ⁻¹ᵁ Q).ι)^*[ModuleCat.{u + 1} Λ])).obj ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K)) :=
  (L((ι ∣_ Q)^*[ModuleCat.{u + 1} Λ])).mapIso
      (leftDerivedUpperStarRightDerivedLowerStarIsoOfEtale Λ
        (isPullback_morphismRestrict j Q).flip K a).symm ≪≫
    ((leftDerivedUpperStarComp _ (ι ∣_ Q) Q.ι).app _).symm ≪≫
    (leftDerivedUpperStarComp _ (ι ⁻¹ᵁ Q).ι ι (ι ∣_ Q ≫ Q.ι)
      (morphismRestrict_ι ι Q)).app _

variable {ℓ}

omit [Finite Λ] in
/-- The property `P(K)`: `ι^* Rj_* K` has finite locally constant cohomology sheaves. It is stable
under shifts. -/
lemma hasFiniteLocallyConstantHomology_shift {W V D : Scheme.{u}} (j : V ⟶ W) (ι : D ⟶ W)
    (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : HasFiniteLocallyConstantHomology D ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj K))) (n : ℤ) :
    HasFiniteLocallyConstantHomology D ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj (K⟦n⟧))) :=
  (hK.shift n).of_iso
    (((R((j)_*[ModuleCat.{u + 1} Λ]) ⋙ L((ι)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).app K).symm

/-- The property `P(K)`: `ι^* Rj_* K` has finite locally constant cohomology sheaves. It is stable
under extensions in distinguished triangles. -/
lemma hasFiniteLocallyConstantHomology_ext {W V D : Scheme.{u}} (j : V ⟶ W) (ι : D ⟶ W)
    (T : Triangle (DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (hT : T ∈ distTriang _)
    (h₁ : HasFiniteLocallyConstantHomology D ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj T.obj₁)))
    (h₃ : HasFiniteLocallyConstantHomology D ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj T.obj₃))) :
    HasFiniteLocallyConstantHomology D ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj T.obj₂)) :=
  HasFiniteLocallyConstantHomology.of_distTriang _
    ((R((j)_*[ModuleCat.{u + 1} Λ]) ⋙ L((ι)^*[ModuleCat.{u + 1} Λ])).map_distinguished T hT) h₁ h₃

omit [Finite Λ] in
/-- Finite local constancy of the cohomology sheaves is preserved by pullback. -/
lemma HasFiniteLocallyConstantHomology.leftDerivedUpperStar {X Y : Scheme.{u}} (g : Y ⟶ X)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : HasFiniteLocallyConstantHomology X K) :
    HasFiniteLocallyConstantHomology Y ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) := fun n ↦
  have := hK n
  have := IsFiniteLocallyConstantSheaf.upperStar g ((DerivedCategory.homologyFunctor _ n).obj K)
  IsFiniteLocallyConstantSheaf.of_iso
    (F := (g)^*[ModuleCat.{u + 1} Λ].obj ((DerivedCategory.homologyFunctor _ n).obj K))
    ((leftDerivedUpperStarHomologyFunctorIso _ g n).app K)

omit [Finite Λ] in
/-- Every complex of étale sheaves on an empty scheme is zero: it has no geometric points. -/
lemma isZero_of_isEmpty {V : Scheme.{u}} [IsEmpty V]
    (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : IsZero K := by
  rw [DerivedCategory.isZero_iff]
  intro q
  rw [IsZero.iff_id_eq_zero]
  exact sheafHom_ext_of_upperStar_map_eq fun Ω _ _ x ↦
    (IsEmpty.false (x (IsLocalRing.closedPoint Ω))).elim

variable (ℓ) in
include hΛ in
/-- **Local constancy of a direct image by dévissage** (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`, *Complexes*): let `j : V ⟶ W` be an open
immersion into a locally noetherian regular scheme and `ι : D ⟶ W` a morphism. If `ι^* Rj_* N_V` has
finite locally constant cohomology sheaves for every finite `Λ`-module `N` killed by `ℓ`, then so
has `ι^* Rj_* E` for every bounded complex `E` on `V` whose cohomology sheaves have finite `ℓ`-group
monodromy. -/
theorem hasFiniteLocallyConstantHomology_of_constantSheaf {W V D : Scheme.{u}}
    [IsLocallyNoetherian W] [IsRegular W] (j : V ⟶ W) [IsOpenImmersion j] (ι : D ⟶ W)
    (hbase : ∀ (N : ModuleCat.{u + 1} Λ), Finite N → (∀ n : N, (ℓ : Λ) • n = 0) →
      HasFiniteLocallyConstantHomology D ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)))))
    (E : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : IsBoundedFiniteEllGroupMonodromy ℓ E) :
    HasFiniteLocallyConstantHomology D ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj E)) := by
  intro n
  let Q : D → W.Opens := fun d ↦ ⟨connectedComponent (ι d), isOpen_connectedComponent⟩
  refine @IsFiniteLocallyConstantSheaf.of_openCover _ _ _ _ _ _ _ _ _ _
    (Scheme.openCoverOfIsOpenCover _ (fun d ↦ ι ⁻¹ᵁ Q d) (eq_top_iff.2 fun d _ ↦
      TopologicalSpace.Opens.mem_iSup.2 ⟨d, mem_connectedComponent⟩)) _ fun d ↦ ?_
  obtain ⟨a, -, ha, -⟩ := hE.1
  let E' := (L(((j ⁻¹ᵁ Q d).ι)^*[ModuleCat.{u + 1} Λ])).obj E
  suffices h : HasFiniteLocallyConstantHomology (ι ⁻¹ᵁ Q d)
      ((L((ι ∣_ Q d)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((j ∣_ Q d)_*[ModuleCat.{u + 1} Λ])).obj E')) by
    have := (h.of_iso (restrictOpensIso j ι (Q d) E a)) n
    exact IsFiniteLocallyConstantSheaf.of_iso (F := (DerivedCategory.homologyFunctor _ n).obj
      ((L(((ι ⁻¹ᵁ Q d).ι)^*[ModuleCat.{u + 1} Λ])).obj ((L((ι)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((j)_*[ModuleCat.{u + 1} Λ])).obj E))))
      ((leftDerivedUpperStarHomologyFunctorIso _ (ι ⁻¹ᵁ Q d).ι n).app _).symm
  by_cases hV : IsEmpty (j ⁻¹ᵁ Q d)
  · intro m
    refine IsFiniteLocallyConstantSheaf.of_isZero (Functor.map_isZero _ ?_)
    exact Functor.map_isZero _ (Functor.map_isZero _ (isZero_of_isEmpty E'))
  rw [not_isEmpty_iff] at hV
  have : ConnectedSpace (Q d) :=
    Subtype.connectedSpace isConnected_connectedComponent
  have : IrreducibleSpace (Q d).toScheme := irreducibleSpace_of_isDomain_stalk _ fun x ↦
    MulEquiv.isDomain _ ((Q d).stalkIso x).commRingCatIsoToRingEquiv.toMulEquiv
  have : ConnectedSpace (j ⁻¹ᵁ Q d) := by
    have hirr : IsIrreducible (Set.range (j ∣_ Q d)) :=
      ⟨Set.range_nonempty _, (IrreducibleSpace.isIrreducible_univ (Q d).toScheme).isPreirreducible
        |>.open_subset (j ∣_ Q d).isOpenEmbedding.isOpen_range (Set.subset_univ _)⟩
    exact connectedSpace_iff_univ.2 ⟨Set.univ_nonempty,
      (j ∣_ Q d).isOpenEmbedding.isInducing.isPreconnected_image.1
        (by rw [Set.image_univ]; exact hirr.2.isPreconnected)⟩
  let P : ObjectProperty (DerivedCategory (Sheaf (j ⁻¹ᵁ Q d).toScheme.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) := fun K ↦
    HasFiniteLocallyConstantHomology (ι ⁻¹ᵁ Q d) ((L((ι ∣_ Q d)^*[ModuleCat.{u + 1} Λ])).obj
      ((R((j ∣_ Q d)_*[ModuleCat.{u + 1} Λ])).obj K))
  have : P.IsClosedUnderIsomorphisms := ⟨fun e hK ↦ hK.of_iso
    ((R((j ∣_ Q d)_*[ModuleCat.{u + 1} Λ]) ⋙ L((ι ∣_ Q d)^*[ModuleCat.{u + 1} Λ])).mapIso e)⟩
  refine prop_of_isBoundedFiniteEllGroupMonodromy ℓ hΛ P
    (fun K m hK ↦ hasFiniteLocallyConstantHomology_shift _ _ K hK m)
    (fun T hT h₁ h₃ ↦ hasFiniteLocallyConstantHomology_ext _ _ T hT h₁ h₃) (fun N hN hℓN ↦ ?_) E'
    ?_
  · let NV := (DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)
    have h := (HasFiniteLocallyConstantHomology.leftDerivedUpperStar (ι ⁻¹ᵁ Q d).ι
      (hbase N hN hℓN)).of_iso
      (restrictOpensIso j ι (Q d) NV 0).symm
    refine h.of_iso (((R((j ∣_ Q d)_*[ModuleCat.{u + 1} Λ]) ⋙
      L((ι ∣_ Q d)^*[ModuleCat.{u + 1} Λ])).mapIso ?_))
    exact (singleFunctorCompLeftDerivedUpperStarIso _ _).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) _).app N)
  · obtain ⟨⟨a', b', ha', hb'⟩, hE'⟩ := hE.mapDerivedCategoryUpperStar (j ⁻¹ᵁ Q d).ι
    let e := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (j ⁻¹ᵁ Q d).ι).app E
    refine ⟨⟨a', b', DerivedCategory.TStructure.t.isGE_of_iso e.symm a',
      DerivedCategory.TStructure.t.isLE_of_iso e.symm b'⟩, fun m ↦ ?_⟩
    exact (hE' m).of_iso ((DerivedCategory.homologyFunctor _ m).mapIso e.symm)

end AlgebraicGeometry.Etale
