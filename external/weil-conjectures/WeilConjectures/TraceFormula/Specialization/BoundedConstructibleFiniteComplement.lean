/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedLocalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
public import WeilConjectures.TraceFormula.Specialization.FinitePointReflection
public import WeilConjectures.TraceFormula.Specialization.SliceSupport

/-!

# Bounded constructibility off a finite closed subscheme

Let `k` be a separably closed field of characteristic `p ≠ ℓ`, `Y` a separated `k`-scheme of
finite type, `j : U ⟶ Y` an open immersion and `i : Z ⟶ Y` a closed immersion onto its
complement with `Z` finite over `k`. A complex `K` of `ℚ̄_ℓ`-sheaves on `Y` such that `Lj^* K` and
`RΓ(Y, K)` are bounded constructible is bounded constructible
(`ProEtale.CondensedRing.boundedConstructible_of_upperStar_of_lowerStar_of_isFinite`).

This is the step of Deligne's criterion (SGA 4½, [Th. finitude], proof of 3.2) controlling the
skyscraper part of the nearby cycles at finitely many closed points by the cohomology. The proof
follows the étale analogue
`AlgebraicGeometry.Etale.boundedConstructible_of_upperStar_of_rightDerivedLowerStar`: in the
open–closed triangle `j_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶`, the first vertex is bounded constructible
and so is its cohomology (Deligne's finiteness), hence so is `R(i ≫ p)_* Li^* K`, and the finite
point reflection (`boundedConstructible_of_boundedConstructible_rightDerivedLowerStar_of_isFinite`
in `ProEtale.CondensedRing`) shows that `Li^* K` is bounded constructible.

For `Y` proper, this assembles Deligne's criterion from its local input
(`ProEtale.CondensedRing.boundedConstructible_of_forall_exists_coordinates_of_lowerStar`): if
`RΓ(Y, C)` is bounded constructible and, locally on `Y`, `C` is bounded constructible away from
the preimages `bᵢ⁻¹(Fᵢ)` of finite sets of closed points under coordinates `bᵢ : U ⟶ 𝔸¹_k` jointly
detecting closed points, then `C` is bounded constructible. For the nearby cycles
`C = Ψ_{ℙⁿ⁺¹}(B)` of the criterion, `RΓ(ℙⁿ⁺¹_s, C) = RΓ(ℙⁿ⁺¹_η̄, B)` is bounded constructible by
the proper exchange. The finitely many fibres may be found pointwise: if `C` is bounded
constructible near every point over the generic point of a coordinate line, it is so away from
finitely many fibres of that coordinate
(`ProEtale.CondensedRing.exists_finset_boundedConstructible_of_forall_isGenericPoint`, by
Chevalley's theorem; assembled in
`ProEtale.CondensedRing.boundedConstructible_of_forall_exists_coordinates_of_isGenericPoint`).
The local input (spreading the bounded constructibility of the restrictions to the geometric
generic fibres of the coordinates to neighbourhoods of those points) is not formalised.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [IsSepClosed k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Bounded constructibility off a finite closed subscheme**: for a separated `k`-scheme `Y` of
finite type (`k` separably closed, `ℓ ≠ char k`), an open `U` of `Y` and a closed immersion
`i : Z ⟶ Y` onto its complement with `Z` finite over `k`, a complex `K` of `ℚ̄_ℓ`-sheaves on `Y`
whose restriction `Lj^* K` to `U` and whose cohomology `RΓ(Y, K) = Rp_* K` are bounded
constructible is bounded constructible. In the open–closed triangle
`j_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶`, `Rp_* j_! Lj^* K` is bounded constructible by Deligne's
finiteness theorem, hence so is `Rp_* Ri_* Li^* K ≅ R(i ≫ p)_* Li^* K`, and `Li^* K` is bounded
constructible by the reflection along the finite morphism `i ≫ p`. -/
theorem boundedConstructible_of_upperStar_of_lowerStar_of_isFinite {Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (U : Y.left.Opens)
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [IsFinite (i ≫ Y.hom)]
    (hiU : IsCompl (Set.range i.base) (Set.range U.ι.base))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)))
    (hU : boundedConstructible _ ((L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K))
    (hΓ : boundedConstructible _ ((R((Y.hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) :
    boundedConstructible _ K := by
  have : IsNoetherian Y.left :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian Y.hom
      __ := QuasiCompact.compactSpace_of_compactSpace Y.hom }
  have : TopologicalSpace.NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  let Λ := Profinite.padicAlgClRingObj ℓ
  let Q := boundedConstructible (condensedRingObj Λ (Spec (.of k)))
  have : Q.IsTriangulated := isTriangulated_boundedConstructible_padicAlgClRingObj _ ℓ
  obtain ⟨δ, hT⟩ := exists_distTriang_openClosed_derived Λ U.ι i hiU K
  have h₁ : boundedConstructible (condensedRingObj Λ Y.left)
      (D((U.ι)_!open⟦Λ⟧).obj ((L((U.ι)^*⟦Λ⟧)).obj K)) :=
    boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj Λ U.ι _ hU
  have hb₁ : Q ((R((Y.hom)_*⟦Λ⟧)).obj (D((U.ι)_!open⟦Λ⟧).obj ((L((U.ι)^*⟦Λ⟧)).obj K))) :=
    boundedConstructible_rightDerivedLowerStar_obj ℓ
      (Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec (.of k)))) ⟨_, h₁⟩
  have hb₃ := Q.ext_of_isTriangulatedClosed₃ _
    ((R((Y.hom)_*⟦Λ⟧)).map_distinguished _ hT) hb₁ hΓ
  have hN : boundedConstructible (condensedRingObj Λ Z) ((L((i)^*⟦Λ⟧)).obj K) :=
    boundedConstructible_of_boundedConstructible_rightDerivedLowerStar_of_isFinite Λ
      (i ≫ Y.hom) _ (Q.prop_of_iso ((rightDerivedLowerStarComp Λ i Y.hom).app _) hb₃)
  exact boundedConstructible_of_openClosed Λ U.ι i hiU.eq_compl K hU hN

/-- If the derived pullback of `C` along an open immersion `g` is bounded constructible, so is its
derived pullback along any morphism `f` whose image lies in the image of `g`: `f` factors through
`g`. -/
lemma boundedConstructible_leftDerivedUpperStar_of_range_subset
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {W V X : Scheme.{u}} (f : W ⟶ X) (g : V ⟶ X) [IsOpenImmersion g]
    (hfg : Set.range f ⊆ Set.range g)
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (h : boundedConstructible _ ((L((g)^*⟦Λ⟧)).obj C)) :
    boundedConstructible _ ((L((f)^*⟦Λ⟧)).obj C) := by
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ g = f := ⟨_, IsOpenImmersion.lift_fac g f hfg⟩
  exact (boundedConstructible _).prop_of_iso ((leftDerivedUpperStarComp Λ l g).app C).symm
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ l _ h)

/-- **Bounded constructibility is local**: on a scheme with noetherian underlying space, a complex
which is bounded constructible on an open neighbourhood of every point is bounded constructible
(finitely many of the neighbourhoods cover, `boundedConstructible_of_openCover`). -/
theorem boundedConstructible_of_forall_exists_opens
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ boundedConstructible _ ((L((W.ι)^*⟦Λ⟧)).obj K)) :
    boundedConstructible _ K := by
  choose W hxW hW using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (W x : Set X))
    (fun x ↦ (W x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxW x⟩)
  let e := t.equivFin
  refine boundedConstructible_of_openCover Λ (fun a ↦ W (e.symm a).1) (fun x ↦ ?_) K
    fun a ↦ hW _
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨e ⟨y, hyt⟩, by simpa using hxy⟩

omit [IsSepClosed k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **Bounded constructibility off finitely many closed points, from coordinates**. Let `Y` be
of finite type over a field `k` and `C` a `ℚ̄_ℓ`-complex on `Y`. Suppose that every point of `Y`
has an open neighbourhood `U` with finitely many coordinates `bᵢ : U ⟶ 𝔸¹_k` such that a point of
`U` all of whose coordinates are closed is closed, and such that for each `i`, `C|_U` is bounded
constructible away from the preimage `bᵢ⁻¹(Fᵢ)` of a finite set `Fᵢ` of closed points. Then `C` is
bounded constructible away from finitely many closed points: as in
`ProEtale.CondensedRing.exists_finset_isZero_of_forall_exists_coordinates`, the set
`⋂ᵢ bᵢ⁻¹(Fᵢ)` is a closed set of closed points of `U`, hence finite. -/
theorem exists_finset_boundedConstructible_of_forall_exists_coordinates
    (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (H : ∀ y : Y.left, ∃ (U : Y.left.Opens) (_ : y ∈ U) (ι : Type u) (_ : Finite ι)
      (b : ι → (U.toScheme ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))),
      (∀ v : U, (∀ i, IsClosed {b i v}) → IsClosed {v}) ∧
      ∀ i, ∃ (F : Finset 𝔸(ULift.{u} (Fin 1); Spec (.of k))) (hF : ∀ x ∈ F, IsClosed {x}),
        boundedConstructible _
          (L(((b i ⁻¹ᵁ finsetComplOpens F hF).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            (L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))) :
    ∃ (S : Finset Y.left) (hS : ∀ x ∈ S, IsClosed {x}),
      boundedConstructible _
        (L(((finsetComplOpens S hS).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C) := by
  have := isNoetherian_left Y
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  choose U hyU ι hι b hcl F hFc hFz using H
  -- the locus `Σ_y = ⋂ᵢ bᵢ⁻¹(Fᵢ)`, a finite set of closed points
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
  -- bounded constructibility on the complement, locally
  have : TopologicalSpace.NoetherianSpace (finsetComplOpens S hS) :=
    IsImmersion.noetherianSpace (finsetComplOpens S hS).ι
  refine boundedConstructible_of_forall_exists_opens (Profinite.padicAlgClRingObj ℓ)
    fun w ↦ ?_
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
  refine (boundedConstructible _).prop_of_iso ((leftDerivedUpperStarComp
    (Profinite.padicAlgClRingObj ℓ) W.ι (finsetComplOpens S hS).ι).app C) ?_
  refine boundedConstructible_leftDerivedUpperStar_of_range_subset
    (Profinite.padicAlgClRingObj ℓ) _ (V.ι ≫ (U y).ι) ?_ ?_
  · rintro _ ⟨v, rfl⟩
    exact v.2
  · exact (boundedConstructible _).prop_of_iso ((leftDerivedUpperStarComp
      (Profinite.padicAlgClRingObj ℓ) V.ι (U y).ι).app C).symm (hFz y i)

omit [IsSepClosed k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **Spreading bounded constructibility from the generic fibre of a coordinate, pointwise**: let
`Y` be of finite type over a field `k`, `b : Y ⟶ 𝔸¹_k` locally of finite type and `C` a complex
on `Y` which is bounded constructible on a neighbourhood of every point of `Y` lying over the
generic point of `𝔸¹_k`. Then `C` is bounded constructible away from the preimage `b⁻¹(F)` of a
finite set `F` of closed points of `𝔸¹_k`. The set `Σ` of points of `Y` with no neighbourhood on
which `C` is bounded constructible is closed, so its image `b(Σ)` is constructible (Chevalley's
theorem) and omits the generic point, hence is a finite set of closed points; and bounded
constructibility is local. -/
theorem exists_finset_boundedConstructible_of_forall_isGenericPoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    {n : Type u} [Unique n] (b : Y.left ⟶ 𝔸(n; Spec (.of k))) [LocallyOfFiniteType b]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left))}
    (h : ∀ y : Y.left, IsGenericPoint (b y) Set.univ →
      ∃ W : Y.left.Opens, y ∈ W ∧ boundedConstructible _ ((L((W.ι)^*⟦Λ⟧)).obj C)) :
    ∃ (F : Finset 𝔸(n; Spec (.of k))) (hF : ∀ x ∈ F, IsClosed {x}),
      boundedConstructible _ (L(((b ⁻¹ᵁ finsetComplOpens F hF).ι)^*⟦Λ⟧).obj C) := by
  have := isNoetherian_left Y
  -- the set `Σ` of points without a neighbourhood on which `C` is bounded constructible
  let bad : Set Y.left :=
    {y | ¬ ∃ W : Y.left.Opens, y ∈ W ∧ boundedConstructible _ ((L((W.ι)^*⟦Λ⟧)).obj C)}
  have hbad : IsClosed bad := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    simp only [bad, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hy
    obtain ⟨W, hyW, hW⟩ := hy
    refine ⟨W, fun z hz ↦ ?_, W.isOpen, hyW⟩
    simp only [bad, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
    exact ⟨W, hz, hW⟩
  have hcons : Topology.IsConstructible bad :=
    Topology.isConstructible_compl.1 ((TopologicalSpace.NoetherianSpace.isCompact _).isConstructible
      hbad.isOpen_compl)
  have : IsLocallyNoetherian 𝔸(n; Spec (.of k)) :=
    isLocallyNoetherian_of_isOpenImmersion (AffineSpace.SpecIso n (.of k)).hom
  have : LocallyOfFinitePresentation b :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  obtain ⟨F, hFs, hF⟩ := AffineSpace.exists_finset_of_isConstructible n k
    (b.isConstructible_image hcons) (by
      rintro _ ⟨y, hy, rfl⟩ hgen
      exact absurd (h y hgen) hy)
  refine ⟨F, hF, ?_⟩
  let V := b ⁻¹ᵁ finsetComplOpens F hF
  have : TopologicalSpace.NoetherianSpace V := IsImmersion.noetherianSpace V.ι
  refine boundedConstructible_of_forall_exists_opens Λ fun w ↦ ?_
  have hw : w.1 ∉ bad := fun hw ↦ by
    have : b w.1 ∈ (F : Set 𝔸(n; Spec (.of k))) := hFs ▸ ⟨w.1, hw, rfl⟩
    exact w.2 this
  simp only [bad, Set.mem_ofPred_eq, not_not] at hw
  obtain ⟨W, hwW, hW⟩ := hw
  refine ⟨V.ι ⁻¹ᵁ W, hwW, ?_⟩
  refine (boundedConstructible _).prop_of_iso
    ((leftDerivedUpperStarComp Λ (V.ι ⁻¹ᵁ W).ι V.ι).app C) ?_
  refine boundedConstructible_leftDerivedUpperStar_of_range_subset Λ _ W.ι ?_ hW
  rintro _ ⟨v, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact v.2

/-- **Deligne's criterion, assembly** (SGA 4½, [Th. finitude], proof of 3.2): let `Y` be proper
over a separably closed field `k` (`ℓ ≠ char k`) and `C` a `ℚ̄_ℓ`-complex on `Y` with bounded
constructible cohomology `RΓ(Y, C)`. Suppose that every point of `Y` has an open neighbourhood `U`
with finitely many coordinates `bᵢ : U ⟶ 𝔸¹_k`, jointly detecting closed points, such that `C|_U`
is bounded constructible away from the preimage `bᵢ⁻¹(Fᵢ)` of a finite set `Fᵢ` of closed points.
Then `C` is bounded constructible: it is so away from a finite set `S` of closed points
(`exists_finset_boundedConstructible_of_forall_exists_coordinates`), and the reduced closed
subscheme on `S` is finite over `k`
(`boundedConstructible_of_upperStar_of_lowerStar_of_isFinite`). -/
theorem boundedConstructible_of_forall_exists_coordinates_of_lowerStar
    (Y : Over (Spec (.of k))) [IsProper Y.hom]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hΓ : boundedConstructible _ ((R((Y.hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj C))
    (H : ∀ y : Y.left, ∃ (U : Y.left.Opens) (_ : y ∈ U) (ι : Type u) (_ : Finite ι)
      (b : ι → (U.toScheme ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))),
      (∀ v : U, (∀ i, IsClosed {b i v}) → IsClosed {v}) ∧
      ∀ i, ∃ (F : Finset 𝔸(ULift.{u} (Fin 1); Spec (.of k))) (hF : ∀ x ∈ F, IsClosed {x}),
        boundedConstructible _
          (L(((b i ⁻¹ᵁ finsetComplOpens F hF).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            (L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))) :
    boundedConstructible _ C := by
  obtain ⟨S, hS, hC⟩ := exists_finset_boundedConstructible_of_forall_exists_coordinates Y H
  have hSc : IsClosed (S : Set Y.left) := by
    rw [← Set.biUnion_of_singleton (S : Set Y.left)]
    exact S.finite_toSet.isClosed_biUnion fun x hx ↦ hS x hx
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨S, hSc⟩ : TopologicalSpace.Closeds Y.left)
  have hrange : Set.range I.subschemeι.base = S := by
    simp [I, Scheme.IdealSheafData.range_subschemeι]
  have : Finite I.subscheme :=
    have : Finite (Set.range I.subschemeι.base) := by rw [hrange]; exact S.finite_toSet
    Finite.of_injective_finite_range I.subschemeι.isClosedEmbedding.injective
  have : IsFinite (I.subschemeι ≫ Y.hom) :=
    (IsFinite.iff_isProper_and_finite_preimage_singleton _).2
      ⟨inferInstance, fun _ ↦ Set.toFinite _⟩
  refine boundedConstructible_of_upperStar_of_lowerStar_of_isFinite (finsetComplOpens S hS)
    I.subschemeι ?_ C hC hΓ
  rw [hrange, Scheme.Opens.range_ι, coe_finsetComplOpens]
  exact isCompl_compl

/-- **Deligne's criterion, pointwise form** (SGA 4½, [Th. finitude], proof of 3.2): let `Y` be
proper over a separably closed field `k` (`ℓ ≠ char k`) and `C` a `ℚ̄_ℓ`-complex on `Y` with
bounded constructible cohomology `RΓ(Y, C)`. Suppose that every point of `Y` has an open
neighbourhood `U` with finitely many coordinates `bᵢ : U ⟶ 𝔸¹_k` locally of finite type, jointly
detecting closed points, such that `C|_U` is bounded constructible on a neighbourhood of every
point of `U` lying over the generic point of a coordinate line. Then `C` is bounded constructible
(`ProEtale.CondensedRing.exists_finset_boundedConstructible_of_forall_isGenericPoint` and
`ProEtale.CondensedRing.boundedConstructible_of_forall_exists_coordinates_of_lowerStar`). -/
theorem boundedConstructible_of_forall_exists_coordinates_of_isGenericPoint
    (Y : Over (Spec (.of k))) [IsProper Y.hom]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hΓ : boundedConstructible _ ((R((Y.hom)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj C))
    (H : ∀ y : Y.left, ∃ (U : Y.left.Opens) (_ : y ∈ U) (ι : Type u) (_ : Finite ι)
      (b : ι → (U.toScheme ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))),
      (∀ i, LocallyOfFiniteType (b i)) ∧ (∀ v : U, (∀ i, IsClosed {b i v}) → IsClosed {v}) ∧
      ∀ i (v : U), IsGenericPoint (b i v) Set.univ →
        ∃ W : U.toScheme.Opens, v ∈ W ∧ boundedConstructible _
          (L((W.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            (L((U.ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C))) :
    boundedConstructible _ C := by
  refine boundedConstructible_of_forall_exists_coordinates_of_lowerStar Y hΓ fun y ↦ ?_
  obtain ⟨U, hyU, ι, hι, b, hb, hcl, hgen⟩ := H y
  refine ⟨U, hyU, ι, hι, b, hcl, fun i ↦ ?_⟩
  have := hb i
  have := isNoetherian_left Y
  have : TopologicalSpace.NoetherianSpace U := IsImmersion.noetherianSpace U.ι
  have := locallyOfFiniteType_overMk_of_isImmersion Y U.ι
  have := quasiCompact_overMk_of_isImmersion Y U.ι
  exact exists_finset_boundedConstructible_of_forall_isGenericPoint
    (Profinite.padicAlgClRingObj ℓ) (Over.mk (U.ι ≫ Y.hom)) (b i) (hgen i)

end AlgebraicGeometry.ProEtale.CondensedRing
