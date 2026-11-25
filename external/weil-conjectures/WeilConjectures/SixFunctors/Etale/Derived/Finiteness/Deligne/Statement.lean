/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Empty

/-!
# The induction statement for Deligne's generic constructibility

The proof of `theorem-generic-constructibility-base-change-rj` is an induction on the dimension of
the generic fibre of the source (`AlgebraicGeometry.Etale.genericFiberDim`). This file states the
induction hypothesis (`AlgebraicGeometry.Etale.DeligneStatement`), proves its start, for an empty
generic fibre (`AlgebraicGeometry.Etale.deligneStatement_zero`), and deduces the theorem from the
induction hypothesis in all dimensions
(`AlgebraicGeometry.Etale.exists_hasConstructibleDirectImageBaseChangeOn_of_forall`). It also
states the input on smooth morphisms with locally constant coefficients of the second step,
`lemma-smooth-morphisms-locally-constant-sheaves`
(`AlgebraicGeometry.Etale.SmoothGenericDirectImage`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The dimension of the generic fibre of a morphism `f : X ⟶ S` to an irreducible scheme, an
empty fibre having dimension `⊥`. -/
noncomputable def genericFiberDim {X S : Scheme.{u}} [IrreducibleSpace S] (f : X ⟶ S) :
    WithBot ℕ∞ :=
  topologicalKrullDim (f.fiber (genericPoint S))

/-- The generic fibre of `f` is empty if and only if its dimension is `⊥`. -/
lemma genericFiberDim_nonneg_of_mem_range {X S : Scheme.{u}} [IrreducibleSpace S] (f : X ⟶ S)
    (h : genericPoint S ∈ Set.range f) : 0 ≤ genericFiberDim f := by
  obtain ⟨x, hx⟩ := h
  have : Nonempty (f.fiber (genericPoint S)) := ⟨(f.fiberHomeo _).symm ⟨x, hx⟩⟩
  have : Nonempty (TopologicalSpace.IrreducibleCloseds (f.fiber (genericPoint S))) :=
    ⟨⟨closure {Classical.arbitrary _}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact Order.krullDim_nonneg

/-- The dimension of the generic fibre does not increase under composition with an immersion. -/
lemma genericFiberDim_comp_le {X' X S : Scheme.{u}} [IrreducibleSpace S] (ι : X' ⟶ X)
    [IsImmersion ι] (f : X ⟶ S) : genericFiberDim (ι ≫ f) ≤ genericFiberDim f := by
  unfold genericFiberDim
  rw [IsHomeomorph.topologicalKrullDim_eq _ ((ι ≫ f).fiberHomeo _).isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo _).isHomeomorph]
  let φ : (ι ≫ f) ⁻¹' {genericPoint S} → f ⁻¹' {genericPoint S} :=
    fun x ↦ ⟨ι x.1, by rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]; exact x.2⟩
  refine Topology.IsInducing.topologicalKrullDim_le (f := φ) ?_
  exact (ι.isEmbedding.isInducing.comp Topology.IsInducing.subtypeVal).codRestrict _

/-- The generic fibre of a morphism of finite type has finite dimension. -/
lemma genericFiberDim_ne_top {X S : Scheme.{u}} [IrreducibleSpace S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] : genericFiberDim f ≠ ⊤ := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (genericPoint S)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : QuasiCompact (f.fiberToSpecResidueField (genericPoint S)) :=
    inferInstanceAs (QuasiCompact (pullback.snd _ _))
  have : CompactSpace (f.fiber (genericPoint S)) :=
    QuasiCompact.compactSpace_of_compactSpace (f.fiberToSpecResidueField (genericPoint S))
  exact topologicalKrullDim_ne_top_of_compactSpace (f.fiberToSpecResidueField (genericPoint S))

/-- An immersion into a locally noetherian scheme is quasi-compact: it is a closed immersion
followed by an open immersion. -/
lemma quasiCompact_of_isImmersion {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (j : X ⟶ Y)
    [IsImmersion j] : QuasiCompact j := by
  rw [← j.liftCoborder_ι]
  infer_instance

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The induction statement** of the proof of `theorem-generic-constructibility-base-change-rj`,
in generic dimension `< n`: for every integral scheme `S` of finite type over a field on which the
exponent of `Λ` is invertible, every immersion `j : X ⟶ Y` of finite type `S`-schemes whose generic
fibre has dimension `< n`, and every constructible sheaf `F` on `X`, there is a nonempty open
`U ⊆ S` over which the direct image of `F` along `j` is bounded constructible and commutes with
every base change from a noetherian scheme. -/
def DeligneStatement (n : ℕ) : Prop :=
  ∀ ⦃k : Type u⦄ [Field k] ⦃S X Y : Scheme.{u}⦄ [IsIntegral S] (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [HasInvertibleExponent Λ S] (fY : Y ⟶ S)
    [LocallyOfFiniteType fY] [QuasiCompact fY] (j : X ⟶ Y) [IsImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F],
    genericFiberDim (j ≫ fY) < n →
      ∃ U : S.Opens, (U : Set S).Nonempty ∧ HasDirectImageBaseChangeOnPlus Λ fY j
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) U

/-- **The smooth case**, the statement of `lemma-smooth-morphisms-locally-constant-sheaves` used by
the proof of `theorem-generic-constructibility-base-change-rj`: for a separated smooth morphism of
finite type `a : X ⟶ S` to an integral scheme of finite type over a field on which the exponent of
`Λ` is invertible, and a finite locally constant sheaf `F` on `X`, there is a nonempty open `U ⊆ S`
over which `Ra_* F` is bounded constructible and commutes with every base change from a
noetherian scheme. -/
def SmoothGenericDirectImage : Prop :=
  ∀ ⦃k : Type u⦄ [Field k] ⦃S X : Scheme.{u}⦄ [IsIntegral S] (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [HasInvertibleExponent Λ S] (a : X ⟶ S)
    [Smooth a] [IsSeparated a] [QuasiCompact a]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F],
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ HasDirectImageBaseChangeOnPlus Λ (𝟙 S) a
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) U

variable {Λ}

/-- **The start of the induction**: an empty generic fibre. -/
theorem deligneStatement_zero : DeligneStatement Λ 0 := by
  intro k _ S X Y _ aS _ _ _ fY _ _ j _ F _ hdim
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (fY ≫ aS)
  have := quasiCompact_of_isImmersion j
  have : IsNoetherian S :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian aS
      __ := QuasiCompact.compactSpace_of_compactSpace aS }
  refine exists_hasDirectImageBaseChangeOnPlus_of_genericPoint_not_mem_range fY j
    (fun h ↦ ?_) _
  have := genericFiberDim_nonneg_of_mem_range _ h
  exact (lt_irrefl _ (this.trans_lt (by exact_mod_cast hdim)))

/-- Every element of `WithBot ℕ∞` other than `⊤` is smaller than a natural number. -/
lemma WithBot.ENat.exists_lt_natCast_of_ne_top {d : WithBot ℕ∞} (hd : d ≠ ⊤) :
    ∃ n : ℕ, d < n := by
  induction d using WithBot.recBotCoe with
  | bot => exact ⟨0, WithBot.bot_lt_coe _⟩
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd rfl hd
    | coe d => exact ⟨d + 1, by exact_mod_cast Nat.lt_succ_self d⟩

/-- **Deligne's generic constructibility from the induction statement in all dimensions**. -/
theorem exists_hasConstructibleDirectImageBaseChangeOn_of_forall
    (h : ∀ n, DeligneStatement Λ n) {k : Type u} [Field k]
    {S X Y : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] [HasInvertibleExponent Λ S] (fY : Y ⟶ S) [LocallyOfFiniteType fY]
    [QuasiCompact fY] (j : X ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      HasConstructibleDirectImageBaseChangeOn Λ fY j F U := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (fY ≫ aS)
  have : QuasiCompact j := inferInstance
  obtain ⟨n, hn⟩ := WithBot.ENat.exists_lt_natCast_of_ne_top (genericFiberDim_ne_top (j ≫ fY))
  obtain ⟨U, hU, hP⟩ := h n aS fY j F hn
  exact ⟨U, hU, (hasConstructibleDirectImageBaseChangeOn_iff fY j F U).2 hP⟩

end Etale

end AlgebraicGeometry
