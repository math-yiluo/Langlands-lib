/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.AffineLineConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLisseDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.StalkZeroLocus
public import WeilConjectures.TraceFormula.Specialization.ClosedPointsSupport

/-!

# Bounded constructible complexes vanishing over the generic point of a curve

Let `Y` be a scheme of finite type over a field `k` and `C` a bounded constructible
`ℚ̄_ℓ`-complex on `Y_proét`. This file proves that `C` has a constructible *support*: a
constructible subset `s ⊆ Y` such that `C` vanishes on every open disjoint from `s`, while `s`
meets the image of no morphism `g : W ⟶ Y` with `Lg^* C = 0`
(`ProEtale.CondensedRing.exists_isConstructible_support`). Consequently, for a morphism
`b : Y ⟶ 𝔸¹_k`, if `C` vanishes after pullback to `Y ×_{𝔸¹} Spec K` for a point
`Spec K ⟶ 𝔸¹_k` over the generic point, then `C` vanishes on `Y ∖ b⁻¹(F)` for a finite set `F`
of closed points of `𝔸¹_k`
(`ProEtale.CondensedRing.exists_finset_isZero_leftDerivedUpperStar_of_isZero_pullback`). This is
the last step of the finite-support part of Gabber's Künneth formula for nearby cycles (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Finite support": the support of the cone has
no point over the generic point of a special-fibre coordinate line; its image in that line is
constructible and omits the generic point, so is a finite set of closed points).

## The argument

The cohomology sheaves `Hᵠ(C)`, finitely many of them nonzero, are constructible: lisse on the
strata `ι : D ⟶ Y` of a stratification. The rank function of the lisse sheaf `ι^* Hᵠ(C)`
(`ProEtale.CondensedRing.fiberRankFun`) is locally constant, `D` being of finite type over `k`, so
the set `T ⊆ D` where it does not vanish is clopen, and `s` is the union of the images `ι(T)`.

* A lisse sheaf with vanishing rank function vanishes: it is locally free of rank given by the
  rank function (`ProEtale.CondensedRing.exists_isOpenImmersion_isFree`), and pro-étale covers
  detect zero objects (`ProEtale.CondensedRing.isZero_of_forall_fiberRankFun_eq_zero`). Hence on
  an open `U` disjoint from `s`, all the restrictions of `Hᵠ(C)|_U` to the strata vanish, and
  so does `Hᵠ(C)|_U` (finitely many quasi-compact jointly surjective pullbacks detect zero).
* If `Lg^* C = 0`, the pullback of `ι^* Hᵠ(C)` to `D ×_Y W` is the pullback of
  `Hᵠ(Lg^* C) = 0`, so it has fibre rank `0` at every point; the rank function of `ι^* Hᵠ(C)`
  vanishes on the points of `D` lying over the image of `g`.

## Main statements

- `ProEtale.CondensedRing.isZero_of_forall_fiberRankFun_eq_zero`: a lisse `ℚ̄_ℓ`-sheaf on a
  scheme of finite type over a field with vanishing rank function is zero.
- `ProEtale.CondensedRing.exists_isConstructible_support`: the constructible support of a bounded
  constructible `ℚ̄_ℓ`-complex.
- `ProEtale.CondensedRing.exists_finset_isZero_leftDerivedUpperStar_of_isZero_pullback`: a bounded
  constructible complex vanishing over the generic point of `𝔸¹_k` vanishes away from the
  preimage of finitely many closed points.

-/

@[expose] public section

universe u

open CategoryTheory Limits Topology ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### Detection of zero objects -/

section Detection

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- A module object over `Λ_X` vanishes if its pullbacks along the members of a pro-étale covering
family vanish. -/
lemma isZero_of_forall_isZero_upperStar_of_mem {X : Scheme.{u}} {ι : Type*}
    {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : ∀ i, IsZero ((g i)^*⟦Λ⟧.obj M)) : IsZero M := by
  refine isZero_of_isZero_X Λ ?_
  have : IsIso (0 : M.X ⟶ 0) := by
    refine isIso_of_isIso_localizationRestriction Ab.{u + 1} (0 : M.X ⟶ 0) g hg fun i ↦ ?_
    have h₁ : IsZero ((g i)^*[Ab.{u + 1}].obj M.X) :=
      ((Mod.forget _).map_isZero (h i)).of_iso (upperStarObjXIso Λ _ M).symm
    have h₂ : IsZero ((g i)^*[Ab.{u + 1}].obj 0) := Functor.map_isZero _ (isZero_zero _)
    have : IsIso ((g i)^*[Ab.{u + 1}].map (0 : M.X ⟶ 0)) :=
      isIso_of_source_target_iso_zero _ h₁.isoZero h₂.isoZero
    exact (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (g i) inferInstance) _).1 this
  exact (isZero_zero _).of_iso (asIso (0 : M.X ⟶ 0))

/-- A module object over `Λ_X` vanishes if its restrictions to the members of an open cover
vanish. -/
lemma isZero_of_forall_isZero_upperStar_opens {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (hU : ∀ x, ∃ i, x ∈ U i)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : ∀ i, IsZero (((U i).ι)^*⟦Λ⟧.obj M)) : IsZero M :=
  isZero_of_isZero_X Λ (ProEtale.isZero_of_forall_isZero_upperStar_obj Ab.{u + 1} U hU M.X
    fun i ↦ ((Mod.forget _).map_isZero (h i)).of_iso (upperStarObjXIso Λ (U i).ι M).symm)

/-- A module object over `Λ_X` vanishes if every point has an open neighbourhood on which it
vanishes. -/
lemma isZero_of_forall_exists_isZero_upperStar_opens {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsZero ((U.ι)^*⟦Λ⟧.obj M)) : IsZero M :=
  isZero_of_forall_isZero_upperStar_opens Λ
    (Subtype.val : {U : X.Opens // IsZero ((U.ι)^*⟦Λ⟧.obj M)} → X.Opens)
    (fun x ↦ let ⟨U, hx, hU⟩ := H x; ⟨⟨U, hU⟩, hx⟩) fun U ↦ U.2

/-- If the pullback of `N` along an open immersion `j` vanishes, so does its restriction to the
open image of `j`. -/
lemma isZero_upperStar_opensRange {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : IsZero ((j)^*⟦Λ⟧.obj N)) : IsZero ((j.opensRange.ι)^*⟦Λ⟧.obj N) := by
  have h₁ : IsZero ((j.isoOpensRange.hom)^*⟦Λ⟧.obj ((j.opensRange.ι)^*⟦Λ⟧.obj N)) :=
    h.of_iso (((upperStarComp Λ j.isoOpensRange.hom j.opensRange.ι).app N).symm ≪≫
      (upperStarCongr Λ j.isoOpensRange_hom_ι).app N)
  exact (((j.isoOpensRange.inv)^*⟦Λ⟧).map_isZero h₁).of_iso (((upperStarId Λ _).app _).symm ≪≫
    (upperStarCongr Λ j.isoOpensRange.inv_hom_id.symm).app _ ≪≫
    (upperStarComp Λ j.isoOpensRange.inv j.isoOpensRange.hom).app _)

end Detection

/-! ### The rank function -/

section FiberRank

variable {X : Scheme.{u}}
  {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)}

/-- If the rank function of `M` vanishes at `g x`, the rank function of `g^* M` vanishes at `x`:
a fibre rank of a pullback of `g^* M` is a fibre rank of a pullback of `M`. -/
lemma fiberRankFun_upperStar_eq_zero {W : Scheme.{u}} (g : W ⟶ X) {x : W}
    (h : fiberRankFun ℓ M (g x) = 0) :
    fiberRankFun ℓ ((g)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M) x = 0 := by
  by_cases hne : {d | ∃ (W' : Scheme.{u}) (g' : W' ⟶ W) (w : W'), g' w = x ∧
      HasFiberRank ℓ ((g')^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj
        ((g)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M)) w d}.Nonempty
  · obtain ⟨W', g', w, hw, H⟩ := Nat.sInf_mem hne
    have H' := H.of_iso ((upperStarComp (Profinite.padicAlgClRingObj.{u} ℓ) g' g).app M).symm
    change sInf _ = 0
    rw [H'.eq_fiberRankFun (g' ≫ g), Scheme.Hom.comp_apply, hw, h]
  · exact Nat.sInf_eq_zero.2 (Or.inr (Set.not_nonempty_iff_eq_empty.1 hne))

/-- If the pullback of `M` along `g` vanishes, the rank function of `M` vanishes on the image of
`g`: the pullback has fibre rank `0`. -/
lemma fiberRankFun_eq_zero_of_isZero_upperStar {W : Scheme.{u}} (g : W ⟶ X)
    (h : IsZero ((g)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M)) (w : W) :
    fiberRankFun ℓ M (g w) = 0 := by
  have h0 := isZero_finiteFree_zero (W := Spec (W.residueField w))
    (Profinite.padicAlgClRingObj.{u} ℓ)
  have H : HasFiberRank ℓ ((g)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧.obj M) w 0 :=
    ⟨(((W.fromSpecResidueField w)^*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧).map_isZero h).iso h0⟩
  exact (H.eq_fiberRankFun g).symm

end FiberRank

/-! ### Lisse sheaves with vanishing rank function -/

section Lisse

variable {k : Type u} [Field k]

/-- **A lisse `ℚ̄_ℓ`-sheaf with vanishing rank function is zero.** Let `M` be a pro-étale locally
finitely presented module over `ℚ̲̄_ℓ` on a scheme `Z` of finite type over a field, whose rank
function vanishes identically. Every point of a member of a pro-étale cover over which `M` is
finitely presented has an open neighbourhood over which `M` is free
(`ProEtale.CondensedRing.exists_isOpenImmersion_isFree`), of rank the value of the rank function,
that is, of rank `0`; and vanishing is local for the pro-étale topology. -/
theorem isZero_of_forall_fiberRankFun_eq_zero (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    {M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Z.left)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left) M)
    (h : ∀ z, fiberRankFun ℓ M z = 0) : IsZero M := by
  obtain ⟨𝒰, h𝒰⟩ := id hM
  have (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  refine isZero_of_forall_isZero_upperStar_of_mem (Profinite.padicAlgClRingObj ℓ) 𝒰.f 𝒰.mem₀
    fun i ↦ isZero_of_forall_exists_isZero_upperStar_opens (Profinite.padicAlgClRingObj ℓ)
      fun y ↦ ?_
  obtain ⟨V, j, _, ⟨v, rfl⟩, d, ⟨e⟩⟩ := exists_isOpenImmersion_isFree Z hM (𝒰.f i)
    (isFinitelyPresented_upperStar_of_isLocallyFinitelyPresented h𝒰 i) y
  have hd : d = 0 :=
    (((hasFiberRank_finiteFree v d).of_iso e.symm).eq_fiberRankFun (j ≫ 𝒰.f i)).trans (h _)
  subst hd
  refine ⟨j.opensRange, ⟨v, rfl⟩, isZero_upperStar_opensRange _ j ?_⟩
  exact ((isZero_finiteFree_zero (Profinite.padicAlgClRingObj ℓ)).of_iso e).of_iso
    ((upperStarComp (Profinite.padicAlgClRingObj ℓ) j (𝒰.f i)).app M).symm

end Lisse

/-! ### The support of a bounded constructible complex -/

section Support

variable {k : Type u} [Field k]

/-- A scheme immersed into a scheme of finite type over `k` is of finite type over `k`. -/
lemma locallyOfFiniteType_overMk_of_isImmersion (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] {D : Scheme.{u}} (i : D ⟶ Y.left) [IsImmersion i] :
    LocallyOfFiniteType (Over.mk (i ≫ Y.hom)).hom :=
  inferInstanceAs (LocallyOfFiniteType (i ≫ Y.hom))

/-- A scheme immersed into a scheme of finite type over `k` is quasi-compact over `k`. -/
lemma quasiCompact_overMk_of_isImmersion (Y : Over (Spec (.of k)))
    {D : Scheme.{u}} (i : D ⟶ Y.left) [TopologicalSpace.NoetherianSpace D] :
    QuasiCompact (Over.mk (i ≫ Y.hom)).hom :=
  inferInstanceAs (QuasiCompact (i ≫ Y.hom))

variable (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

/-- The locus where the rank function of a lisse `ℚ̄_ℓ`-sheaf on a scheme immersed into `Y` does
not vanish is clopen: the rank function is locally constant. -/
lemma isClopen_setOf_fiberRankFun_ne_zero {D : Scheme.{u}} (ι : D ⟶ Y.left) [IsImmersion ι]
    {N : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) D)}
    (hN : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D) N) :
    IsClopen {d | fiberRankFun ℓ N d ≠ 0} := by
  have := isNoetherian_left Y
  have := IsImmersion.noetherianSpace ι
  have := locallyOfFiniteType_overMk_of_isImmersion Y ι
  have := quasiCompact_overMk_of_isImmersion Y ι
  exact ((isLocallyConstant_fiberRankFun (Over.mk (ι ≫ Y.hom)) hN).isClopen_fiber 0).compl

/-- The image in `Y` of the locus where the rank function of a lisse `ℚ̄_ℓ`-sheaf on a scheme
immersed into `Y` does not vanish is constructible (Chevalley's theorem). -/
lemma isConstructible_image_setOf_fiberRankFun_ne_zero {D : Scheme.{u}} (ι : D ⟶ Y.left)
    [IsImmersion ι]
    {N : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) D)}
    (hN : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) D) N) :
    IsConstructible (ι '' {d | fiberRankFun ℓ N d ≠ 0}) := by
  have := isNoetherian_left Y
  have := IsImmersion.noetherianSpace ι
  have : LocallyOfFinitePresentation ι :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  exact ι.isConstructible_image
    (isClopen_setOf_fiberRankFun_ne_zero Y ι hN).isClosed.isConstructible_of_noetherianSpace

/-- **Vanishing on an open from the rank functions on the strata.** Let `G` be a `ℚ̄_ℓ`-sheaf on
`Y`, lisse on the strata `ι : D ⟶ Y` of a stratification, and `U` an open of `Y` such that the
rank function of `ι^* G` vanishes at the points of `D` mapping into `U`. Then `G|_U = 0`: the
restriction of `ι^* G` to `ι⁻¹ U` is lisse with vanishing rank function, hence zero
(`ProEtale.CondensedRing.isZero_of_forall_fiberRankFun_eq_zero`), and the finitely many
quasi-compact restrictions `ι⁻¹ U ⟶ U` of the strata jointly cover `U`. -/
lemma isZero_upperStar_of_forall_fiberRankFun_eq_zero
    (G : Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))
    (S : Scheme.Stratification Y.left)
    (hS : ∀ i, IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (S.domain i))
      ((S.immersion i)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj G))
    (U : Y.left.Opens)
    (hU : ∀ i d, S.immersion i d ∈ U →
      fiberRankFun ℓ ((S.immersion i)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj G) d = 0) :
    IsZero ((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj G) := by
  have := isNoetherian_left Y
  have (i : Fin S.n) : TopologicalSpace.NoetherianSpace (S.domain i) :=
    IsImmersion.noetherianSpace (S.immersion i)
  have hz (i : Fin S.n) : IsZero ((S.immersion i ∣_ U)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj
      ((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj G)) := by
    refine IsZero.of_iso ?_
      (upperStarRestrictIso (Profinite.padicAlgClRingObj ℓ) (S.immersion i) U G).symm
    have := locallyOfFiniteType_overMk_of_isImmersion Y ((S.immersion i ⁻¹ᵁ U).ι ≫ S.immersion i)
    have : TopologicalSpace.NoetherianSpace (S.immersion i ⁻¹ᵁ U) :=
      IsImmersion.noetherianSpace ((S.immersion i ⁻¹ᵁ U).ι ≫ S.immersion i)
    have := quasiCompact_overMk_of_isImmersion Y ((S.immersion i ⁻¹ᵁ U).ι ≫ S.immersion i)
    exact isZero_of_forall_fiberRankFun_eq_zero
      (Over.mk (((S.immersion i ⁻¹ᵁ U).ι ≫ S.immersion i) ≫ Y.hom))
      (IsLocallyFinitelyPresented.upperStar (Profinite.padicAlgClRingObj ℓ)
        (S.immersion i ⁻¹ᵁ U).ι (hS i)) fun v ↦
        fiberRankFun_upperStar_eq_zero (S.immersion i ⁻¹ᵁ U).ι (hU i _ v.2)
  have hg : ∀ x, ∃ i, x ∈ Set.range (S.immersion i ∣_ U) := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (S.iUnion_stratum_eq_univ ▸ Set.mem_univ (U.ι x))
    rw [← S.range_immersion i] at hi
    obtain ⟨d, hd⟩ := hi
    have hdU : d ∈ S.immersion i ⁻¹ᵁ U := by
      change S.immersion i d ∈ U
      rw [hd]
      exact x.2
    refine ⟨i, ⟨d, hdU⟩, Subtype.ext ?_⟩
    rw [morphismRestrict_base_coe]
    exact hd
  refine isZero_of_isZero_X (Profinite.padicAlgClRingObj ℓ) ((IsZero.iff_id_eq_zero _).2 ?_)
  refine ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp
    (fun i ↦ S.immersion i ∣_ U) hg _ fun i ↦ ?_
  have h₁ := ((Mod.forget _).map_isZero (hz i)).of_iso
    (upperStarObjXIso (Profinite.padicAlgClRingObj ℓ) (S.immersion i ∣_ U) _).symm
  exact h₁.eq_of_src _ _

/-- **The constructible support of a constructible `ℚ̄_ℓ`-sheaf.** Let `G` be a constructible
`ℚ̄_ℓ`-sheaf on a scheme `Y` of finite type over a field. There is a constructible subset `s ⊆ Y`
such that `G` vanishes on every open disjoint from `s`, and such that `s` is disjoint from the
image of every morphism `g` with `g^* G = 0`: the union, over the strata `ι : D ⟶ Y` of a
stratification on which `G` is lisse, of the images of the clopen subsets of `D` where the rank
function of `ι^* G` does not vanish. -/
theorem exists_isConstructible_support_of_isConstructibleModuleObject
    {G : Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)}
    (hG : IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)
      G) :
    ∃ s : Set Y.left, IsConstructible s ∧
      (∀ U : Y.left.Opens, Disjoint (U : Set Y.left) s →
        IsZero ((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj G)) ∧
      (∀ (W : Scheme.{u}) (g : W ⟶ Y.left),
        IsZero ((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj G) → Disjoint (Set.range g) s) := by
  obtain ⟨S, hS⟩ := hG
  have hM (i : Fin S.n) :=
    (isLocallyFinitelyPresented_mapMod_iff (Profinite.padicAlgClRingObj ℓ) _ G).1 (hS i)
  refine ⟨⋃ i, S.immersion i '' {d | fiberRankFun ℓ
    ((S.immersion i)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj G) d ≠ 0}, ?_, ?_, ?_⟩
  · exact IsConstructible.iUnion fun i ↦
      isConstructible_image_setOf_fiberRankFun_ne_zero Y _ (hM i)
  · intro U hU
    refine isZero_upperStar_of_forall_fiberRankFun_eq_zero Y G S hM U fun i d hd ↦ ?_
    by_contra hne
    exact Set.disjoint_left.1 hU hd (Set.mem_iUnion.2 ⟨i, d, hne, rfl⟩)
  · intro W g hg
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨w, rfl⟩ hs
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hs
    obtain ⟨d, hd, hdw⟩ := hi
    obtain ⟨p, hp₁, -⟩ := Scheme.Pullback.exists_preimage_pullback d w hdw
    have hz := (((pullback.snd (S.immersion i) g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map_isZero
      hg).of_iso (upperStarSquareIso (Profinite.padicAlgClRingObj ℓ) pullback.condition G)
    have := fiberRankFun_eq_zero_of_isZero_upperStar _ hz p
    rw [hp₁] at this
    exact hd this

/-- **The constructible support of a bounded constructible `ℚ̄_ℓ`-complex.** Let `C` be a bounded
constructible `ℚ̄_ℓ`-complex on a scheme `Y` of finite type over a field. There is a constructible
subset `s ⊆ Y` such that `C` vanishes on every open disjoint from `s`, and such that `s` is disjoint
from the image of every morphism `g` with `Lg^* C = 0`: the union of the supports
(`ProEtale.CondensedRing.exists_isConstructible_support_of_isConstructibleModuleObject`) of the
finitely many nonzero cohomology sheaves of `C`, the derived pullbacks commuting with the
cohomology sheaves. Blueprint `proposition-external-kunneth-formula-nearby-cycles`, "Finite
support". -/
theorem exists_isConstructible_support
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left) C) :
    ∃ s : Set Y.left, IsConstructible s ∧
      (∀ U : Y.left.Opens, Disjoint (U : Set Y.left) s →
        IsZero (L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) ∧
      (∀ (W : Scheme.{u}) (g : W ⟶ Y.left),
        IsZero (L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) → Disjoint (Set.range g) s) := by
  obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff _ C).1 hC
  choose s hs hU hW using fun q ↦ exists_isConstructible_support_of_isConstructibleModuleObject Y
    (hc q)
  refine ⟨⋃ q : Finset.Icc a b, s q, IsConstructible.iUnion fun q ↦ hs q, ?_, ?_⟩
  · intro U hU'
    refine isZero_of_forall_isZero_homology (Profinite.padicAlgClRingObj ℓ) fun q ↦ ?_
    refine IsZero.of_iso ?_
      ((leftDerivedUpperStarHomologyIso (Profinite.padicAlgClRingObj ℓ) U.ι q).app C).symm
    by_cases hq : q ∈ Finset.Icc a b
    · exact hU q U (Set.disjoint_of_subset_right
        (Set.subset_iUnion (fun q : Finset.Icc a b ↦ s q) ⟨q, hq⟩) hU')
    · refine (Functor.map_isZero ((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧) (hab q ?_) :)
      simp only [Finset.mem_Icc, not_and_or, not_le] at hq
      exact hq
  · intro W g hg
    refine Set.disjoint_iUnion_right.2 fun q ↦ hW q W g ?_
    exact ((DerivedCategory.homologyFunctor _ q).map_isZero hg).of_iso
      ((leftDerivedUpperStarHomologyIso (Profinite.padicAlgClRingObj ℓ) g q).app C)

end Support

/-! ### Vanishing over the generic point of the affine line -/

section AffineLine

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom]

/-- **A bounded constructible complex vanishing over the generic point of a line vanishes away
from finitely many fibres.** Let `Y` be of finite type over a field `k`, `b : Y ⟶ 𝔸¹_k` locally of
finite type, and `C` a bounded constructible `ℚ̄_ℓ`-complex on `Y`. Let `g : W ⟶ Y` be a morphism
whose image contains every point of `Y` lying over the generic point of `𝔸¹_k`. If `Lg^* C = 0`,
then there is a finite set `F` of closed points of `𝔸¹_k` such that `C` vanishes on
`Y ∖ b⁻¹(F)`.

Indeed the constructible support `s` of `C`
(`ProEtale.CondensedRing.exists_isConstructible_support`)
has no point over the generic point, so its image `b(s)`, constructible by Chevalley's theorem,
is a finite set of closed points. Blueprint `proposition-external-kunneth-formula-nearby-cycles`,
"Finite support". -/
theorem exists_finset_isZero_leftDerivedUpperStar_of_isZero_of_range
    {n : Type u} [Unique n] (b : Y.left ⟶ 𝔸(n; Spec (.of k))) [LocallyOfFiniteType b]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left) C)
    {W : Scheme.{u}} (g : W ⟶ Y.left)
    (hg : ∀ y : Y.left, IsGenericPoint (b y) Set.univ → y ∈ Set.range g)
    (h : IsZero (L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) :
    ∃ (F : Finset 𝔸(n; Spec (.of k))) (hF : ∀ x ∈ F, IsClosed {x}),
      IsZero (L(((b ⁻¹ᵁ finsetComplOpens F hF).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) := by
  have := isNoetherian_left Y
  obtain ⟨s, hs, hU, hW⟩ := exists_isConstructible_support Y hC
  have : IsLocallyNoetherian 𝔸(n; Spec (.of k)) :=
    isLocallyNoetherian_of_isOpenImmersion (AffineSpace.SpecIso n (.of k)).hom
  have : LocallyOfFinitePresentation b :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  obtain ⟨F, hFs, hF⟩ := AffineSpace.exists_finset_of_isConstructible n k
    (b.isConstructible_image hs) (by
      rintro _ ⟨y, hy, rfl⟩ hgen
      exact Set.disjoint_left.1 (hW W g h) (hg y hgen) hy)
  refine ⟨F, hF, hU _ (Set.disjoint_right.2 fun y hy hyU ↦ ?_)⟩
  have : b y ∈ (F : Set 𝔸(n; Spec (.of k))) := hFs ▸ ⟨y, hy, rfl⟩
  exact hyU this

/-- **A bounded constructible complex vanishing over the generic point of a line vanishes away
from finitely many fibres** (blueprint `proposition-external-kunneth-formula-nearby-cycles`, "Finite
support"). Let `Y` be of finite type over a field `k`, `b : Y ⟶ 𝔸¹_k` locally of finite type, `C` a
bounded constructible `ℚ̄_ℓ`-complex on `Y`, and `ξ : Spec K ⟶ 𝔸¹_k` a point over the generic point.
If the pullback of `C` to `Y ×_{𝔸¹} Spec K` vanishes, then `C` vanishes on `Y ∖ b⁻¹(F)` for a
finite set `F` of closed points of `𝔸¹_k`: every point of `Y` over the generic point lifts to
`Y ×_{𝔸¹} Spec K`. -/
theorem exists_finset_isZero_leftDerivedUpperStar_of_isZero_pullback
    {n : Type u} [Unique n] (b : Y.left ⟶ 𝔸(n; Spec (.of k))) [LocallyOfFiniteType b]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left) C)
    {K : Type u} [Field K] (ξ : Spec (.of K) ⟶ 𝔸(n; Spec (.of k))) {t : Spec (.of K)}
    (hξ : IsGenericPoint (ξ t) Set.univ)
    (h : IsZero (L((pullback.fst b ξ)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) :
    ∃ (F : Finset 𝔸(n; Spec (.of k))) (hF : ∀ x ∈ F, IsClosed {x}),
      IsZero (L(((b ⁻¹ᵁ finsetComplOpens F hF).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) := by
  refine exists_finset_isZero_leftDerivedUpperStar_of_isZero_of_range Y b hC _ (fun y hy ↦ ?_) h
  obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback y t (hy.eq hξ)
  exact ⟨p, hp⟩

end AffineLine

end AlgebraicGeometry.ProEtale.CondensedRing
