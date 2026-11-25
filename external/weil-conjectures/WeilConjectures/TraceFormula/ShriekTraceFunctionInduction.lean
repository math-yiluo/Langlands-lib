/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.VanishingIdealSubschemeIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive
public import WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage

/-!

# Noetherian induction for the sheaf–function compatibility of the Weil lower shriek

The sheaf–function compatibility `ProEtale.CondensedRing.ShriekTraceFunctionAt` of the Weil
lower shriek holds along every morphism `f : X ⟶ Y` as soon as it holds *generically*: every
nonempty `X` with an automorphism `e_X` of finite order has a nonempty `e_X`-stable open
subscheme `U` on which it holds along `U ⟶ X ⟶ Y`
(`ProEtale.CondensedRing.ShriekTraceFunctionGenericallyHolds`).

The proof is a Noetherian induction on the closed subsets `T` of `X` which are the range of an
`e_X`-stable closed subscheme `Z`. Given the generic open `U` of `Z`, the reduced induced closed
subscheme `Z'` on its complement carries the automorphism induced by `e_Z`
(`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdealSubschemeIso`); its range in `X` is a
strictly smaller closed subset, and the dévissage
`ProEtale.CondensedRing.shriekTraceFunctionAt_of_isCompl` along `U ⊔ Z' = Z` concludes. The
induction starts with the empty scheme, over which every complex of sheaves is zero
(`ProEtale.CondensedRing.shriekTraceFunctionAt_of_isEmpty`).

## Main results

- `ProEtale.CondensedRing.shriekTraceFunctionAt_of_exists_isOpenImmersion`: the compatibility
  along every `f` with `e_X` of finite order, from the generic hypothesis.
- `ProEtale.CondensedRing.weilShriekTraceFunction_of_genericallyHolds`: the statement of
  `ProEtale.CondensedRing.weilShriekTraceFunction`, from the generic hypothesis.

-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The empty scheme -/

section Empty

/-- Every sheaf of abelian groups on the pro-étale site of an empty scheme is zero: its sections
over every object, an empty scheme, are terminal. -/
lemma isZero_sheaf_proEt_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (G : Sheaf (ProEt.topology X) Ab.{u + 1}) : IsZero G := by
  refine (IsZero.iff_id_eq_zero G).2 (Sheaf.hom_ext (NatTrans.ext (funext fun T ↦ ?_)))
  have : IsEmpty T.unop.left := ⟨fun x ↦ isEmptyElim (α := X) (T.unop.hom.base x)⟩
  exact (ProEt.isTerminalSectionsOfIsEmpty G T.unop).hom_ext _ _

/-- Every module object over a ring object on the pro-étale site of an empty scheme is zero. -/
lemma isZero_mod_proEt_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    {R : Sheaf (ProEt.topology X) Ab.{u + 1}} [MonObj R]
    (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) : IsZero M :=
  (IsZero.iff_id_eq_zero _).2 (by
    ext : 1
    exact (isZero_sheaf_proEt_of_isEmpty M.X).eq_of_src _ _)

/-- Every object of the derived category of module objects on the pro-étale site of an empty
scheme is zero: all its homology objects are zero. -/
lemma isZero_derivedCategory_proEt_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (K : DerivedCategory (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)) :
    IsZero K := by
  have : K.IsLE 0 := (K.isLE_iff 0).2 fun i _ ↦ isZero_mod_proEt_of_isEmpty _
  have : K.IsGE 1 := (K.isGE_iff 1).2 fun i _ ↦ isZero_mod_proEt_of_isEmpty _
  exact DerivedCategory.TStructure.t.isZero K 0 1

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (eX : X ≅ X) (eY : Y ≅ Y)

/-- **The empty scheme**: the sheaf–function compatibility holds along every `f : X ⟶ Y` with
`X` empty. Both sides vanish: `X` has no points, and `Rf_! K` is zero, every complex on `X`
being zero (`isZero_derivedCategory_proEt_of_isEmpty`). -/
theorem shriekTraceFunctionAt_of_isEmpty [IsEmpty X.left] {f : X ⟶ Y}
    (hf : eX.hom ≫ f = f ≫ eY.hom) : ShriekTraceFunctionAt ℓ eX eY hf := by
  intro K n y
  have : IsEmpty (frobeniusFixedPoints eX (n + 1)) := ⟨fun x ↦ isEmptyElim (x.1.base default)⟩
  rw [finsum_of_isEmpty, weilStalkTraceAlternatingSum]
  refine finsum_eq_zero_of_forall_eq_zero fun j ↦ ?_
  have hK : IsZero ((weilLowerShriek ℓ eX eY hf).obj K).carrier :=
    (boundedConstructibleLowerShriek ℓ f).map_isZero
      (IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
        (isZero_derivedCategory_proEt_of_isEmpty _ K.carrier.obj))
  suffices h : weilSheafStalkTrace ℓ (n + 1) y.1 y.2.2
      ((WeilBoundedConstructible.homologyFunctor ℓ eY j).obj
        ((weilLowerShriek ℓ eX eY hf).obj K)) = 0 by
    rw [h, smul_zero]
  refine traceOrZero_eq_zero_of_isZero ?_ _
  rw [Functor.id_obj, WeilSheaf.frobeniusStalk, WeilSheaf.powStalkFunctor, Functor.comp_obj,
    WeilSheaf.stalkFunctor_obj_carrier, WeilSheaf.powFunctor_obj, WeilSheaf.pow_carrier,
    WeilBoundedConstructible.homologyFunctor_obj_carrier]
  exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero (ObjectProperty.ι _) hK))

end Empty

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Transport along an equality of morphisms -/

/-- The sheaf–function compatibility along `f` only depends on `f`, not on the proof of
`e_X ≫ f = f ≫ e_Y`. -/
lemma ShriekTraceFunctionAt.of_eq {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] {eX : X ≅ X} {eY : Y ≅ Y} {f f' : X ⟶ Y}
    {hf : eX.hom ≫ f = f ≫ eY.hom} {hf' : eX.hom ≫ f' = f' ≫ eY.hom} (h : f = f')
    (H : ShriekTraceFunctionAt ℓ eX eY hf) : ShriekTraceFunctionAt ℓ eX eY hf' := by
  subst h
  exact H

/-! ### The reduced complement of a stable open subscheme -/

section Complement

omit [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {Z U : Over (Spec (.of k))} (j : U ⟶ Z) [IsOpenImmersion j.left]

/-- The complement of the range of an open immersion `j : U ⟶ Z`, a closed subset of `Z`. -/
def rangeCompl : Closeds Z.left :=
  ⟨(Set.range j.left.base)ᶜ, j.left.isOpenEmbedding.isOpen_range.isClosed_compl⟩

/-- The reduced induced closed subscheme on the complement of an open immersion `j : U ⟶ Z`,
as a scheme over `Spec k`. -/
noncomputable def reducedCompl : Over (Spec (.of k)) :=
  Over.mk ((IdealSheafData.vanishingIdeal (rangeCompl j)).subschemeι ≫ Z.hom)

/-- The closed immersion of the reduced complement of an open immersion `j : U ⟶ Z`. -/
noncomputable def reducedComplι : reducedCompl j ⟶ Z :=
  Over.homMk (IdealSheafData.vanishingIdeal (rangeCompl j)).subschemeι

instance : IsClosedImmersion (reducedComplι j).left :=
  inferInstanceAs (IsClosedImmersion (IdealSheafData.vanishingIdeal (rangeCompl j)).subschemeι)

instance [LocallyOfFiniteType Z.hom] : LocallyOfFiniteType (reducedCompl j).hom :=
  inferInstanceAs (LocallyOfFiniteType
    ((IdealSheafData.vanishingIdeal (rangeCompl j)).subschemeι ≫ Z.hom))

instance [QuasiCompact Z.hom] : QuasiCompact (reducedCompl j).hom :=
  inferInstanceAs (QuasiCompact
    ((IdealSheafData.vanishingIdeal (rangeCompl j)).subschemeι ≫ Z.hom))

instance [IsSeparated Z.hom] : IsSeparated (reducedCompl j).hom :=
  inferInstanceAs (IsSeparated
    ((IdealSheafData.vanishingIdeal (rangeCompl j)).subschemeι ≫ Z.hom))

lemma range_reducedComplι :
    Set.range (reducedComplι j).left.base = (Set.range j.left.base)ᶜ :=
  IdealSheafData.range_vanishingIdeal_subschemeι _

lemma isCompl_range_reducedComplι :
    IsCompl (Set.range j.left.base) (Set.range (reducedComplι j).left.base) := by
  rw [range_reducedComplι]
  exact isCompl_compl

variable {eZ : Z ≅ Z} {eU : U ≅ U} {j}

/-- The complement of the range of an open immersion stable under `e_Z` is stable under
`e_Z`. -/
lemma image_rangeCompl (hj : eU.hom ≫ j = j ≫ eZ.hom) :
    ((Over.forget _).mapIso eZ).hom.base '' (rangeCompl j : Set Z.left) =
      (rangeCompl j : Set Z.left) := by
  have hb : Function.Bijective eZ.hom.left.base :=
    (homeoOfIso ((Over.forget _).mapIso eZ)).bijective
  have hs : Function.Surjective eU.hom.left.base :=
    (homeoOfIso ((Over.forget _).mapIso eU)).surjective
  have h : eZ.hom.left.base '' Set.range j.left.base = Set.range j.left.base := by
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, ← Over.comp_left, ← hj,
      Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hs.range_eq,
      Set.image_univ]
  exact (Set.image_compl_eq hb).trans (congrArg _ h)

/-- The automorphism of the reduced complement of an `e_Z`-stable open immersion induced by
`e_Z`. -/
noncomputable def reducedComplIso (hj : eU.hom ≫ j = j ≫ eZ.hom) :
    reducedCompl j ≅ reducedCompl j :=
  Over.isoMk (IdealSheafData.vanishingIdealSubschemeIso (Z := rangeCompl j) (W := rangeCompl j) _
    (image_rangeCompl hj)) (by
    simp only [reducedCompl, Over.mk_hom]
    rw [IdealSheafData.vanishingIdealSubschemeIso_hom_subschemeι_assoc, Functor.mapIso_hom,
      Over.forget_map, Over.w])

lemma reducedComplIso_hom_comp_reducedComplι (hj : eU.hom ≫ j = j ≫ eZ.hom) :
    (reducedComplIso hj).hom ≫ reducedComplι j = reducedComplι j ≫ eZ.hom :=
  Over.OverMorphism.ext (IdealSheafData.vanishingIdealSubschemeIso_hom_subschemeι _
    (image_rangeCompl hj))

end Complement

/-! ### The Noetherian induction -/

variable (k) in
/-- The sheaf–function compatibility *holds generically*: for every morphism `f : X ⟶ Y` of
separated schemes of finite type over `Spec k`, automorphisms `e_X`, `e_Y` with
`e_X ≫ f = f ≫ e_Y` and `e_X` of finite order, if `X` is nonempty, there is a nonempty
`e_X`-stable open subscheme `j : U ⟶ X` along which the compatibility holds for `j ≫ f`. -/
def ShriekTraceFunctionGenericallyHolds : Prop :=
  ∀ (X Y : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom),
    (∃ m : ℕ, eX.pow (m + 1) = Iso.refl X) → Nonempty X.left →
    ∃ (U : Over (Spec (.of k))) (_ : LocallyOfFiniteType U.hom) (_ : QuasiCompact U.hom)
      (_ : IsSeparated U.hom) (eU : U ≅ U) (j : U ⟶ X) (_ : IsOpenImmersion j.left)
      (hj : eU.hom ≫ j = j ≫ eX.hom),
      Nonempty U.left ∧ ShriekTraceFunctionAt ℓ eU eY (comp_comm_of_comp_comm eU eY eX hj hf)

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The inductive step: the compatibility along `i ≫ f` for an `e_X`-stable closed immersion
`i : Z ⟶ X`, assuming it along the `e_X`-stable closed immersions with strictly smaller
range. -/
lemma shriekTraceFunctionAt_closedImmersion_of_lt (H : ShriekTraceFunctionGenericallyHolds ℓ k)
    (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    (he : ∃ m : ℕ, eX.pow (m + 1) = Iso.refl X) (T : Closeds X.left)
    (ih : ∀ T' < T, ∀ (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
      [IsSeparated Z.hom] (eZ : Z ≅ Z) (i : Z ⟶ X) [IsClosedImmersion i.left]
      (hi : eZ.hom ≫ i = i ≫ eX.hom), Set.range i.left.base = T' →
      ShriekTraceFunctionAt ℓ eZ eY (comp_comm_of_comp_comm eZ eY eX hi hf))
    (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (eZ : Z ≅ Z) (i : Z ⟶ X) [IsClosedImmersion i.left]
    (hi : eZ.hom ≫ i = i ≫ eX.hom) (hT : Set.range i.left.base = T) :
    ShriekTraceFunctionAt ℓ eZ eY (comp_comm_of_comp_comm eZ eY eX hi hf) := by
  have heZ := exists_pow_eq_refl_of_mono eX hi he
  rcases isEmpty_or_nonempty Z.left with hZ | hZ
  · exact shriekTraceFunctionAt_of_isEmpty ℓ eZ eY _
  obtain ⟨U, _, _, _, eU, j, _, hj, ⟨u⟩, HU⟩ :=
    H Z Y eZ eY (i ≫ f) (comp_comm_of_comp_comm eZ eY eX hi hf) heZ hZ
  refine shriekTraceFunctionAt_of_isCompl ℓ eZ eY eU (reducedComplIso hj) _ hj
    (reducedComplIso_hom_comp_reducedComplι hj) (isCompl_range_reducedComplι j) heZ HU ?_
  have : IsClosedImmersion (reducedComplι j ≫ i).left :=
    inferInstanceAs (IsClosedImmersion ((reducedComplι j).left ≫ i.left))
  refine ShriekTraceFunctionAt.of_eq ℓ (Category.assoc _ _ _) (ih ⟨_,
    (reducedComplι j ≫ i).left.isClosedEmbedding.isClosed_range⟩ ?_ _ (reducedComplIso hj)
    (reducedComplι j ≫ i) (comp_comm_of_comp_comm _ _ _
      (reducedComplIso_hom_comp_reducedComplι hj) hi) rfl)
  rw [← SetLike.coe_ssubset_coe, Closeds.coe_mk, ← hT, Over.comp_left, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp]
  refine (Set.image_subset_range _ _).ssubset_of_ne fun h ↦ ?_
  have hu : i.left.base (j.left.base u) ∈
      i.left.base '' Set.range (reducedComplι j).left.base :=
    h ▸ Set.mem_range_self _
  obtain ⟨w, hw, hwu⟩ := hu
  rw [range_reducedComplι, i.left.isClosedEmbedding.injective hwu] at hw
  exact hw (Set.mem_range_self u)

/-- **Noetherian induction**: if every nonempty `X` (with `e_X` of finite order) has a nonempty
`e_X`-stable open `U` on which the compatibility holds along `j ≫ f`, it holds along every
`f`. -/
theorem shriekTraceFunctionAt_of_exists_isOpenImmersion
    (H : ShriekTraceFunctionGenericallyHolds ℓ k) (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y}
    (hf : eX.hom ≫ f = f ≫ eY.hom) (he : ∃ m : ℕ, eX.pow (m + 1) = Iso.refl X) :
    ShriekTraceFunctionAt ℓ eX eY hf := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have key (T : Closeds X.left) : ∀ (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
      [QuasiCompact Z.hom] [IsSeparated Z.hom] (eZ : Z ≅ Z) (i : Z ⟶ X)
      [IsClosedImmersion i.left] (hi : eZ.hom ≫ i = i ≫ eX.hom), Set.range i.left.base = T →
      ShriekTraceFunctionAt ℓ eZ eY (comp_comm_of_comp_comm eZ eY eX hi hf) := by
    induction T using WellFoundedLT.induction with
    | _ T ih => exact shriekTraceFunctionAt_closedImmersion_of_lt ℓ H eX eY hf he T ih
  have : IsClosedImmersion (𝟙 X : X ⟶ X).left := inferInstanceAs (IsClosedImmersion (𝟙 X.left))
  exact ShriekTraceFunctionAt.of_eq ℓ (Category.id_comp f)
    (key ⊤ X eX (𝟙 X) (by simp) (by simp))

/-- The sheaf–function compatibility of the Weil lower shriek
(`ProEtale.CondensedRing.weilShriekTraceFunction`), assuming that it holds generically. -/
theorem weilShriekTraceFunction_of_genericallyHolds (H : ShriekTraceFunctionGenericallyHolds ℓ k)
    (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    (he : ∃ m : ℕ, eX.pow (m + 1) = Iso.refl X)
    (K : WeilBoundedConstructible ℓ eX.hom) (n : ℕ) (y : frobeniusFixedPoints eY (n + 1)) :
    weilStalkTraceAlternatingSum ℓ (n + 1) y.1 y.2.2 ((weilLowerShriek ℓ eX eY hf).obj K) =
      ∑ᶠ x : {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1},
        weilStalkTraceAlternatingSum ℓ (n + 1) x.1.1 x.1.2.2 K :=
  shriekTraceFunctionAt_of_exists_isOpenImmersion ℓ H eX eY hf he K n y

end AlgebraicGeometry.ProEtale.CondensedRing
