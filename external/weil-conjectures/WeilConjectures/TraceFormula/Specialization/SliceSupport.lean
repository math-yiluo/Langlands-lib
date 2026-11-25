/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedPointsFiberProduct
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethLocal
public import WeilConjectures.TraceFormula.Specialization.GenericVanishing

/-!

# Finite support from vanishing over the generic points of coordinate lines

Let `Y` be a scheme of finite type over a field `k` and `C` a bounded constructible
`ℚ̄_ℓ`-complex on `Y`. Suppose that every point of `Y` has an open neighbourhood `U` with finitely
many *coordinates* `bᵢ : U ⟶ 𝔸¹_k`, jointly detecting closed points (a point of `U` all of whose
coordinates are closed points is closed, as for the components of a quasi-finite map
`U ⟶ 𝔸ⁿ_k`), such that `C|_U` vanishes over the generic point of each coordinate line. Then `C`
is supported on finitely many closed points
(`ProEtale.CondensedRing.exists_finset_isZero_of_forall_exists_coordinates`).

This is the assembly of the finite-support step of Gabber's Künneth formula for nearby cycles
(blueprint `proposition-external-kunneth-formula-nearby-cycles`, "Finite support"): by
`ProEtale.CondensedRing.exists_finset_isZero_leftDerivedUpperStar_of_isZero_pullback`, `C|_U`
vanishes away from the preimage `bᵢ⁻¹(Fᵢ)` of a finite set `Fᵢ` of closed points of the line; the
support of `C|_U` is contained in `⋂ᵢ bᵢ⁻¹(Fᵢ)`, a closed set of closed points of `U`, hence finite;
and finitely many such neighbourhoods cover `Y`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- If the derived pullback of `C` along an open immersion `g` vanishes, so does its derived
pullback along any morphism `f` whose image lies in the image of `g`: `f` factors through `g`. -/
lemma isZero_leftDerivedUpperStar_of_range_subset
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {W V X : Scheme.{u}} (f : W ⟶ X) (g : V ⟶ X) [IsOpenImmersion g]
    (hfg : Set.range f ⊆ Set.range g)
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (h : IsZero (L((g)^*⟦Λ⟧).obj C)) : IsZero (L((f)^*⟦Λ⟧).obj C) := by
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ g = f := ⟨_, IsOpenImmersion.lift_fac g f hfg⟩
  exact (L((l)^*⟦Λ⟧).map_isZero h).of_iso ((leftDerivedUpperStarComp Λ l g).app C)

variable {k : Type u} [Field k]

/-- Vanishing over the generic point of one coordinate line, on an open `U` of `Y`: if the
pullback of `C|_U` to `U ×_{𝔸¹} Spec K` vanishes for a point `Spec K ⟶ 𝔸¹_k` over the generic
point, then `C|_U` vanishes away from the preimage of a finite set of closed points
(`ProEtale.CondensedRing.exists_finset_isZero_leftDerivedUpperStar_of_isZero_pullback`). -/
lemma exists_finset_isZero_opens_of_isZero_pullback (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left) C)
    (U : Y.left.Opens) (b : U.toScheme ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))
    (hb : LocallyOfFiniteType b)
    (h : ∃ (K : Type u) (_ : Field K) (ξ : Spec (.of K) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))
      (t : Spec (.of K)), IsGenericPoint (ξ t) Set.univ ∧
        IsZero (L((pullback.fst b ξ)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))) :
    ∃ (F : Finset 𝔸(ULift.{u} (Fin 1); Spec (.of k))) (hF : ∀ x ∈ F, IsClosed {x}),
      IsZero (L(((b ⁻¹ᵁ finsetComplOpens F hF).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) := by
  obtain ⟨K, _, ξ, t, ht, hz⟩ := h
  have := isNoetherian_left Y
  have := IsImmersion.noetherianSpace U.ι
  have := locallyOfFiniteType_overMk_of_isImmersion Y U.ι
  have := quasiCompact_overMk_of_isImmersion Y U.ι
  exact exists_finset_isZero_leftDerivedUpperStar_of_isZero_pullback
    (Over.mk (U.ι ≫ Y.hom)) b
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ hC) ξ ht hz

/-- **Finite support from vanishing over the generic points of coordinate lines** (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, "Finite support"). Let `Y` be of finite type
over a field `k` and `C` a bounded constructible `ℚ̄_ℓ`-complex on `Y`. Suppose that every point of
`Y` has an open neighbourhood `U` with finitely many coordinates `bᵢ : U ⟶ 𝔸¹_k`, locally of finite
type, such that a point of `U` all of whose coordinates are closed is closed, and such that for each
`i` the pullback of `C|_U` to `U ×_{𝔸¹} Spec Kᵢ` vanishes for some point `Spec Kᵢ ⟶ 𝔸¹_k` over the
generic point. Then `C` vanishes away from finitely many closed points.

By `ProEtale.CondensedRing.exists_finset_isZero_leftDerivedUpperStar_of_isZero_pullback`, `C|_U`
vanishes away from `bᵢ⁻¹(Fᵢ)` for finite sets `Fᵢ` of closed points; the set `⋂ᵢ bᵢ⁻¹(Fᵢ)` is
closed in `U` and consists of closed points, so it is finite
(`Scheme.finite_of_isClosed_of_forall_isClosed_singleton`), and its points are closed in `Y`
(`Y` is a Jacobson space). Finitely many of the neighbourhoods `U` cover `Y`. -/
theorem exists_finset_isZero_of_forall_exists_coordinates (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left) C)
    (H : ∀ y : Y.left, ∃ (U : Y.left.Opens) (_ : y ∈ U) (ι : Type u) (_ : Finite ι)
      (b : ι → (U.toScheme ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))),
      (∀ i, LocallyOfFiniteType (b i)) ∧ (∀ v : U, (∀ i, IsClosed {b i v}) → IsClosed {v}) ∧
      ∀ i, ∃ (K : Type u) (_ : Field K) (ξ : Spec (.of K) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))
        (t : Spec (.of K)), IsGenericPoint (ξ t) Set.univ ∧
        IsZero (L((pullback.fst (b i) ξ)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))) :
    ∃ (S : Finset Y.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsZero (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) := by
  have := isNoetherian_left Y
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  choose U hyU ι hι b hb hcl hgen using H
  -- the finite sets of closed points of the coordinate lines
  choose F hFc hFz using fun y i ↦
    exists_finset_isZero_opens_of_isZero_pullback Y hC (U y) (b y i) (hb y i) (hgen y i)
  -- the support of `C|_U` is contained in the finite set `Σ_y = ⋂ᵢ bᵢ⁻¹(Fᵢ)` of closed points
  let supp : ∀ y, Set (U y) := fun y ↦ {v | ∀ i, b y i v ∈ F y i}
  have hsuppcl : ∀ y, ∀ v ∈ supp y, IsClosed ({v} : Set (U y)) := fun y v hv ↦
    hcl y v fun i ↦ hFc y i _ (hv i)
  have hsuppfin : ∀ y, (supp y).Finite := by
    intro y
    have := IsImmersion.noetherianSpace (U y).ι
    have := locallyOfFiniteType_overMk_of_isImmersion Y (U y).ι
    have := quasiCompact_overMk_of_isImmersion Y (U y).ι
    have := hι y
    refine Scheme.finite_of_isClosed_of_forall_isClosed_singleton ((U y).ι ≫ Y.hom) ?_
      (hsuppcl y)
    have : supp y = ⋂ i, (b y i) ⁻¹' (F y i : Set _) := by ext v; simp [supp]
    rw [this]
    refine isClosed_iInter fun i ↦ ?_
    refine IsClosed.preimage (b y i).continuous ?_
    simpa using (finsetComplOpens (F y i) (hFc y i)).isOpen.isClosed_compl
  -- finitely many neighbourhoods cover `Y`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ ((U y : Set Y.left)))
    (fun y ↦ (U y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyU y⟩)
  have hfin : (⋃ y ∈ t, (Subtype.val '' supp y : Set Y.left)).Finite :=
    t.finite_toSet.biUnion fun y _ ↦ (hsuppfin y).image _
  let S := hfin.toFinset
  have hS : ∀ x ∈ S, IsClosed {x} := by
    intro x hx
    simp only [S, Set.Finite.mem_toFinset, Set.mem_iUnion] at hx
    obtain ⟨y, -, v, hv, rfl⟩ := hx
    refine isClosed_singleton_of_isLocallyClosed_singleton ?_
    rw [← Set.image_singleton]
    exact (hsuppcl y v hv).isLocallyClosed.image (U y).isOpenEmbedding'.isInducing
      (U y).isOpenEmbedding'.isOpen_range.isLocallyClosed
  refine ⟨S, hS, ?_⟩
  -- vanishing on the complement, locally
  have : TopologicalSpace.NoetherianSpace (finsetComplOpens S hS) :=
    IsImmersion.noetherianSpace (finsetComplOpens S hS).ι
  refine isZero_of_forall_exists_isZero_upperStar (Profinite.padicAlgClRingObj ℓ) _ fun w ↦ ?_
  obtain ⟨y, hyt, hwy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ w.1))
  have hnot : (⟨w.1, hwy⟩ : U y) ∉ supp y := by
    intro hsupp
    refine w.2 ?_
    simp only [S, Set.Finite.coe_toFinset, Set.mem_iUnion]
    exact ⟨y, hyt, _, hsupp, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, b y i ⟨w.1, hwy⟩ ∉ F y i := by
    by_contra hc
    push Not at hc
    exact hnot hc
  let V := (b y i) ⁻¹ᵁ finsetComplOpens (F y i) (hFc y i)
  let W := (finsetComplOpens S hS).ι ⁻¹ᵁ (V.ι ≫ (U y).ι).opensRange
  refine ⟨W, ⟨⟨⟨w.1, hwy⟩, hi⟩, rfl⟩, ?_⟩
  refine IsZero.of_iso ?_ ((leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) W.ι
    (finsetComplOpens S hS).ι).app C).symm
  refine isZero_leftDerivedUpperStar_of_range_subset (Profinite.padicAlgClRingObj ℓ) _
    (V.ι ≫ (U y).ι) ?_ ?_
  · rintro _ ⟨v, rfl⟩
    exact v.2
  · exact (hFz y i).of_iso ((leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) V.ι
      (U y).ι).app C)

end AlgebraicGeometry.ProEtale.CondensedRing
