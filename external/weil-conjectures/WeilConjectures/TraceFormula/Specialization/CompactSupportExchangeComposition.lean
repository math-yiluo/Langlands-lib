/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCompose
public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchangeRefinement

/-!

# Compact-support exchanges along a composite of open immersions

Let `ν_C = χ_P⁻¹ ∘ R'_{P*}(ν_ι)` be the compact-support exchange of a compactification
`ι : N ⊆ P` (blueprint `prose-E-15` (3); `ν_ι` the adjoint of the inverse of the
pullback exchange `α_ι`, `χ_P` the proper exchange). This file proves, in abstract categories, the
formal steps showing that for an open sub-model `j : N ⊆ M` and a compactification `ι : M ⊆ P`,
the compact-support exchange of the compactification `j ≫ ι : N ⊆ P` is the composite of the
exchange `ν_j` and of the compact-support exchange of `ι`:

* `ProEtale.CondensedRing.lowerShriekExchangeOfInv_eq_mateEquiv_symm`: `ν_h` is the mate of
  `α_h⁻¹`;
* `ProEtale.CondensedRing.mateEquiv_whiskerLeft_comp_comp_whiskerRight_app`: mates are
  transported along isomorphisms of left adjoints and the conjugate isomorphisms of the right
  adjoints;
* `ProEtale.CondensedRing.lowerShriekExchangeOfInv_comp_app`: the composition law
  `ν_{jι} = ι'_!(ν_j) ∘ ν_ι(j_!)` through the conjugates of the composition isomorphisms of the
  pullbacks, from the composition law of the pullback exchanges;
* `ProEtale.CondensedRing.compactSupportExchangeAux_lift_comp_app`: the composition law of the
  compact-support exchanges `ν_{a_N} = ν_{a_M}(Rj_!) ∘ Ra'_!(ν_j)`, on the shape
  `compactSupportExchangeAux` with restricted functors.

-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Mate

variable {DC DC' DP DP' : Type*} [Category DC] [Category DC'] [Category DP] [Category DP']

/-- The exchange `ν_h` adjoint to the inverse of an invertible pullback exchange `α` is the mate
of `α⁻¹`. -/
lemma lowerShriekExchangeOfInv_eq_mateEquiv_symm {ΨC : DC ⥤ DC'} {ΨP : DP ⥤ DP'}
    {Dh : DC ⥤ DP} {Lh : DP ⥤ DC} {Dh' : DC' ⥤ DP'} {Lh' : DP' ⥤ DC'} (adj : Dh ⊣ Lh)
    (adj' : Dh' ⊣ Lh') (α : ΨP ⋙ Lh' ⟶ Lh ⋙ ΨC) [IsIso α] :
    lowerShriekExchangeOfInv adj adj' α = (mateEquiv adj adj').symm (inv α) := by
  ext X
  simp [lowerShriekExchangeOfInv]

/-- **Transport of mates along isomorphisms of left adjoints**: for isomorphisms `e : LA ≅ LB`,
`e' : LA' ≅ LB'` of left adjoints, the mate of `e' ∘ ν ∘ e⁻¹` (for `adjA`, `adjA'`) is the mate
of `ν` (for `adjB`, `adjB'`) read through the conjugate isomorphisms `RA ≅ RB`, `RA' ≅ RB'`. -/
lemma mateEquiv_whiskerLeft_comp_comp_whiskerRight_app {A B A' B' : Type*} [Category A]
    [Category B] [Category A'] [Category B'] {LA LB : A ⥤ B} {RA RB : B ⥤ A}
    {LA' LB' : A' ⥤ B'} {RA' RB' : B' ⥤ A'} (adjA : LA ⊣ RA) (adjB : LB ⊣ RB)
    (adjA' : LA' ⊣ RA') (adjB' : LB' ⊣ RB') (e : LA ≅ LB) (e' : LA' ≅ LB') {G : A ⥤ A'}
    {H : B ⥤ B'} (ν : G ⋙ LB' ⟶ LB ⋙ H) (b : B) :
    (mateEquiv adjA adjA' (Functor.whiskerLeft G e'.hom ≫ ν ≫
        Functor.whiskerRight e.inv H)).app b =
      G.map ((conjugateIsoEquiv adjA adjB e.symm).hom.app b) ≫ (mateEquiv adjB adjB' ν).app b ≫
        (conjugateIsoEquiv adjA' adjB' e'.symm).inv.app (H.obj b) := by
  have h := conjugateEquiv_mateEquiv_vcomp adjA adjB adjA' e.inv
    ((TwoSquare.mk _ _ _ _ ν).whiskerRight e'.hom)
  rw [mateEquiv_conjugateEquiv_vcomp adjB adjB' adjA' (TwoSquare.mk _ _ _ _ ν) e'.hom] at h
  simpa using congr_arg (fun t ↦ t.app b) h

end Mate

section Composition

variable {DC DC' DX DX' DP DP' : Type*} [Category DC] [Category DC'] [Category DX]
  [Category DX'] [Category DP] [Category DP']

/-- **The composition law of the exchanges `ν_h`**: for adjunctions `Dj ⊣ Lj`, `Dι ⊣ Lι`,
`Djι ⊣ Ljι` (and their primed versions) with composition isomorphisms `c : Ljι ≅ Lι ⋙ Lj`,
`c' : Ljι' ≅ Lι' ⋙ Lj'`, and pullback exchanges satisfying the composition law `hα`, the
exchange `ν_{jι}` adjoint to `α_{jι}⁻¹` is the composite `ι'_!(ν_j) ∘ ν_ι(j_!)` through the
conjugates `Djι ≅ Dj ⋙ Dι` of `c` and `c'`. -/
lemma lowerShriekExchangeOfInv_comp_app {ΨC : DC ⥤ DC'} {ΨX : DX ⥤ DX'} {ΨP : DP ⥤ DP'}
    {Dj : DC ⥤ DX} {Lj : DX ⥤ DC} {Dj' : DC' ⥤ DX'} {Lj' : DX' ⥤ DC'}
    {Dι : DX ⥤ DP} {Lι : DP ⥤ DX} {Dι' : DX' ⥤ DP'} {Lι' : DP' ⥤ DX'}
    {Djι : DC ⥤ DP} {Ljι : DP ⥤ DC} {Djι' : DC' ⥤ DP'} {Ljι' : DP' ⥤ DC'}
    (adjj : Dj ⊣ Lj) (adjj' : Dj' ⊣ Lj') (adjι : Dι ⊣ Lι) (adjι' : Dι' ⊣ Lι')
    (adjjι : Djι ⊣ Ljι) (adjjι' : Djι' ⊣ Ljι') (c : Ljι ≅ Lι ⋙ Lj) (c' : Ljι' ≅ Lι' ⋙ Lj')
    (αj : ΨX ⋙ Lj' ⟶ Lj ⋙ ΨC) [IsIso αj] (αι : ΨP ⋙ Lι' ⟶ Lι ⋙ ΨX) [IsIso αι]
    (αjι : ΨP ⋙ Ljι' ⟶ Ljι ⋙ ΨC) [IsIso αjι]
    (hα : ∀ A, αjι.app A ≫ ΨC.map (c.hom.app A) =
      c'.hom.app (ΨP.obj A) ≫ Lj'.map (αι.app A) ≫ αj.app (Lι.obj A))
    (K : DC) :
    (lowerShriekExchangeOfInv adjjι adjjι' αjι).app K ≫
        ΨP.map ((((conjugateIsoEquiv adjjι (adjj.comp adjι)).symm c).symm).hom.app K) =
      (((conjugateIsoEquiv adjjι' (adjj'.comp adjι')).symm c').symm).hom.app (ΨC.obj K) ≫
        Dι'.map ((lowerShriekExchangeOfInv adjj adjj' αj).app K) ≫
        (lowerShriekExchangeOfInv adjι adjι' αι).app (Dj.obj K) := by
  set E := ((conjugateIsoEquiv adjjι (adjj.comp adjι)).symm c).symm
  set E' := ((conjugateIsoEquiv adjjι' (adjj'.comp adjι')).symm c').symm
  set νj := lowerShriekExchangeOfInv adjj adjj' αj
  set νι := lowerShriekExchangeOfInv adjι adjι' αι
  -- the composite candidate `E⁻¹ ∘ ι'_!(ν_j) ∘ ν_ι(j_!) ∘ E'`, whose mate is `α_{jι}⁻¹`
  let ν : ΨC ⋙ Djι' ⟶ Djι ⋙ ΨP := Functor.whiskerLeft ΨC E'.hom ≫
    Functor.whiskerRight νj Dι' ≫ Functor.whiskerLeft Dj νι ≫ Functor.whiskerRight E.inv ΨP
  have hν : ν = lowerShriekExchangeOfInv adjjι adjjι' αjι := by
    have hm : (mateEquiv adjjι adjjι' ν) = inv αjι := by
      ext A
      have h := mateEquiv_app_comp_conjugateIsoEquiv_hom_app adjj adjι adjjι adjj' adjι' adjjι'
        E E' νj νι ν (fun a ↦ by simp [ν]) A
      simp only [E, E', Iso.symm_symm_eq, Equiv.apply_symm_apply, νj, νι,
        lowerShriekExchangeOfInv_eq_mateEquiv_symm] at h
      rw [← cancel_mono (c'.hom.app _)]
      erw [h]
      rw [← cancel_epi (αjι.app A), reassoc_of% hα]
      simp
    rw [lowerShriekExchangeOfInv_eq_mateEquiv_symm, ← hm]
    exact ((mateEquiv _ _).symm_apply_apply _).symm
  rw [← hν]
  simp [ν]

end Composition

section Shape

variable {DC DC' DX DX' DP DP' Ds Ds' : Type*} [Category DC] [Category DC'] [Category DX]
  [Category DX'] [Category DP] [Category DP'] [Category Ds] [Category Ds']

/-- **The composition law of the compact-support exchanges, on the shape
`compactSupportExchangeAux`** with restricted functors (lifts of ambient ones along full
subcategories, with the compatibilities `ObjectProperty.liftCompιIso`): let `ν_N` and `ν_M` be the
compact-support exchanges of compactifications `N ⊆ P` (through `DhN`) and `M ⊆ P` (through
`DhM`) with the same proper part (`Rp`, `χ`), and `ν_j : Ψ_N ⋙ Dj' ⟶ Dj ⋙ Ψ_M` an exchange of
restricted functors, with composition isomorphisms `lsc : LSfN ≅ Dj ⋙ LSfM`,
`lsc' : LSfN' ≅ Dj' ⋙ LSfM'`. If at every object the identities `H` hold for some
`e : DhN K ⟶ DhM (Dj K)` and `e' : DhN' Ψ_N K ⟶ DhM' (Dj' Ψ_N K)`, then
`ν_N ∘ Ψ_s(lsc) = ν_M(Dj) ∘ LSfM'(ν_j) ∘ lsc'`. -/
lemma compactSupportExchangeAux_lift_comp_app {PC : ObjectProperty DC}
    {PC' : ObjectProperty DC'} {PX : ObjectProperty DX} {PX' : ObjectProperty DX'}
    {PP : ObjectProperty DP} {PP' : ObjectProperty DP'} {Ps : ObjectProperty Ds}
    {Ps' : ObjectProperty Ds'} {ΨC : DC ⥤ DC'} {ΨX : DX ⥤ DX'} {ΨP : DP ⥤ DP'}
    {Ψs : Ds ⥤ Ds'} (hSpC : ∀ X, PC' ((PC.ι ⋙ ΨC).obj X)) (hSpX : ∀ X, PX' ((PX.ι ⋙ ΨX).obj X))
    (hT : ∀ X, Ps' ((Ps.ι ⋙ Ψs).obj X)) {DhN : DC ⥤ DP} {DhN' : DC' ⥤ DP'}
    {DhM : DX ⥤ DP} {DhM' : DX' ⥤ DP'} {Rp : DP ⥤ Ds} {Rp' : DP' ⥤ Ds'}
    (hON : ∀ X, PP ((PC.ι ⋙ DhN).obj X)) (hON' : ∀ X, PP' ((PC'.ι ⋙ DhN').obj X))
    (hOM : ∀ X, PP ((PX.ι ⋙ DhM).obj X)) (hOM' : ∀ X, PP' ((PX'.ι ⋙ DhM').obj X))
    (hR : ∀ X, Ps ((PP.ι ⋙ Rp).obj X)) (hR' : ∀ X, Ps' ((PP'.ι ⋙ Rp').obj X))
    {LSfN : PC.FullSubcategory ⥤ Ps.FullSubcategory}
    {LSfN' : PC'.FullSubcategory ⥤ Ps'.FullSubcategory}
    {LSfM : PX.FullSubcategory ⥤ Ps.FullSubcategory}
    {LSfM' : PX'.FullSubcategory ⥤ Ps'.FullSubcategory}
    (i₁N : LSfN' ≅ PP'.lift (PC'.ι ⋙ DhN') hON' ⋙ Ps'.lift (PP'.ι ⋙ Rp') hR')
    (i₂N : LSfN ≅ PP.lift (PC.ι ⋙ DhN) hON ⋙ Ps.lift (PP.ι ⋙ Rp) hR)
    (i₁M : LSfM' ≅ PP'.lift (PX'.ι ⋙ DhM') hOM' ⋙ Ps'.lift (PP'.ι ⋙ Rp') hR')
    (i₂M : LSfM ≅ PP.lift (PX.ι ⋙ DhM) hOM ⋙ Ps.lift (PP.ι ⋙ Rp) hR)
    (νhN : ΨC ⋙ DhN' ⟶ DhN ⋙ ΨP) (νhM : ΨX ⋙ DhM' ⟶ DhM ⋙ ΨP)
    (χ : Rp ⋙ Ψs ⟶ ΨP ⋙ Rp') (hχ : IsIsoOn PP.ι χ)
    {Dj : PC.FullSubcategory ⥤ PX.FullSubcategory}
    {Dj' : PC'.FullSubcategory ⥤ PX'.FullSubcategory}
    (νj : PC'.lift (PC.ι ⋙ ΨC) hSpC ⋙ Dj' ⟶ Dj ⋙ PX'.lift (PX.ι ⋙ ΨX) hSpX)
    (lsc : LSfN ≅ Dj ⋙ LSfM) (lsc' : LSfN' ≅ Dj' ⋙ LSfM')
    (H : ∀ M : PC.FullSubcategory, ∃ (e : DhN.obj M.obj ⟶ DhM.obj (Dj.obj M).obj)
      (e' : DhN'.obj (ΨC.obj M.obj) ⟶ DhM'.obj (Dj'.obj ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M)).obj),
      νhN.app M.obj ≫ ΨP.map e =
        e' ≫ DhM'.map (νj.app M).hom ≫ νhM.app (Dj.obj M).obj ∧
      (i₁N.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M)).hom ≫ Rp'.map e' =
        (lsc'.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M)).hom ≫
          (i₁M.hom.app (Dj'.obj ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M))).hom ∧
      (i₂N.inv.app M ≫ lsc.hom.app M).hom = Rp.map e ≫ (i₂M.inv.app (Dj.obj M)).hom)
    (M : PC.FullSubcategory) :
    (compactSupportExchangeAux Ps'.fullyFaithfulι i₁N i₂N (PC'.liftCompιIso _ hSpC)
        (PP'.liftCompιIso _ hON') (Ps'.liftCompιIso _ hR') (PP.liftCompιIso _ hON)
        (Ps.liftCompιIso _ hR) (Ps'.liftCompιIso _ hT) νhN (invOnSubcategory PP.ι χ hχ)).app M ≫
        (Ps'.lift (Ps.ι ⋙ Ψs) hT).map (lsc.hom.app M) =
      lsc'.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M) ≫ LSfM'.map (νj.app M) ≫
        (compactSupportExchangeAux Ps'.fullyFaithfulι i₁M i₂M (PX'.liftCompιIso _ hSpX)
          (PP'.liftCompιIso _ hOM') (Ps'.liftCompιIso _ hR') (PP.liftCompιIso _ hOM)
          (Ps.liftCompιIso _ hR) (Ps'.liftCompιIso _ hT) νhM
          (invOnSubcategory PP.ι χ hχ)).app (Dj.obj M) := by
  obtain ⟨e, e', h1, h2, h3⟩ := H M
  have : IsIso (χ.app (DhN.obj M.obj)) := hχ ((PP.lift (PC.ι ⋙ DhN) hON).obj M)
  have : IsIso (χ.app (DhM.obj (Dj.obj M).obj)) := hχ ((PP.lift (PX.ι ⋙ DhM) hOM).obj (Dj.obj M))
  have hχe : (invOnSubcategory PP.ι χ hχ).app ((PP.lift (PC.ι ⋙ DhN) hON).obj M) ≫
      Ψs.map (Rp.map e) = Rp'.map (ΨP.map e) ≫
        (invOnSubcategory PP.ι χ hχ).app ((PP.lift (PX.ι ⋙ DhM) hOM).obj (Dj.obj M)) := by
    rw [← cancel_mono (χ.app (DhM.obj (Dj.obj M).obj)), Category.assoc, Category.assoc]
    erw [χ.naturality e, invOnSubcategory_app_comp_assoc, invOnSubcategory_app_comp]
    simp
  have hi : (LSfM'.map (νj.app M)).hom ≫ (i₁M.hom.app _).hom =
      (i₁M.hom.app _).hom ≫ Rp'.map (DhM'.map (νj.app M).hom) :=
    congr_arg InducedCategory.Hom.hom (i₁M.hom.naturality (νj.app M))
  apply Ps'.fullyFaithfulι.map_injective
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, compactSupportExchangeAux_app,
    compactSupportExchangeAux_app]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj,
    ObjectProperty.ι_map, ObjectProperty.liftCompιIso_hom_app, CategoryTheory.Functor.map_id,
    ObjectProperty.liftCompιIso_inv_app, ObjectProperty.lift_map, Functor.comp_map,
    ObjectProperty.homMk_hom, Category.id_comp, Category.assoc]
  rw [← Ψs.map_comp, ← ObjectProperty.FullSubcategory.comp_hom, h3, Ψs.map_comp,
    reassoc_of% hχe, ← Rp'.map_comp_assoc, h1]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h2, ← reassoc_of% hi]

/-- `compactSupportExchangeAux_lift_comp_app` for transformations `νN`, `νM` equal to the shapes
`compactSupportExchangeAux …` (e.g. definitions unfolding to them, with the restricted functors
under other names). -/
lemma compactSupportExchangeAux_lift_comp_app_of_eq {PC : ObjectProperty DC}
    {PC' : ObjectProperty DC'} {PX : ObjectProperty DX} {PX' : ObjectProperty DX'}
    {PP : ObjectProperty DP} {PP' : ObjectProperty DP'} {Ps : ObjectProperty Ds}
    {Ps' : ObjectProperty Ds'} {ΨC : DC ⥤ DC'} {ΨX : DX ⥤ DX'} {ΨP : DP ⥤ DP'}
    {Ψs : Ds ⥤ Ds'} (hSpC : ∀ X, PC' ((PC.ι ⋙ ΨC).obj X)) (hSpX : ∀ X, PX' ((PX.ι ⋙ ΨX).obj X))
    (hT : ∀ X, Ps' ((Ps.ι ⋙ Ψs).obj X)) {DhN : DC ⥤ DP} {DhN' : DC' ⥤ DP'}
    {DhM : DX ⥤ DP} {DhM' : DX' ⥤ DP'} {Rp : DP ⥤ Ds} {Rp' : DP' ⥤ Ds'}
    (hON : ∀ X, PP ((PC.ι ⋙ DhN).obj X)) (hON' : ∀ X, PP' ((PC'.ι ⋙ DhN').obj X))
    (hOM : ∀ X, PP ((PX.ι ⋙ DhM).obj X)) (hOM' : ∀ X, PP' ((PX'.ι ⋙ DhM').obj X))
    (hR : ∀ X, Ps ((PP.ι ⋙ Rp).obj X)) (hR' : ∀ X, Ps' ((PP'.ι ⋙ Rp').obj X))
    {LSfN : PC.FullSubcategory ⥤ Ps.FullSubcategory}
    {LSfN' : PC'.FullSubcategory ⥤ Ps'.FullSubcategory}
    {LSfM : PX.FullSubcategory ⥤ Ps.FullSubcategory}
    {LSfM' : PX'.FullSubcategory ⥤ Ps'.FullSubcategory}
    (i₁N : LSfN' ≅ PP'.lift (PC'.ι ⋙ DhN') hON' ⋙ Ps'.lift (PP'.ι ⋙ Rp') hR')
    (i₂N : LSfN ≅ PP.lift (PC.ι ⋙ DhN) hON ⋙ Ps.lift (PP.ι ⋙ Rp) hR)
    (i₁M : LSfM' ≅ PP'.lift (PX'.ι ⋙ DhM') hOM' ⋙ Ps'.lift (PP'.ι ⋙ Rp') hR')
    (i₂M : LSfM ≅ PP.lift (PX.ι ⋙ DhM) hOM ⋙ Ps.lift (PP.ι ⋙ Rp) hR)
    (νhN : ΨC ⋙ DhN' ⟶ DhN ⋙ ΨP) (νhM : ΨX ⋙ DhM' ⟶ DhM ⋙ ΨP)
    (χ : Rp ⋙ Ψs ⟶ ΨP ⋙ Rp') (hχ : IsIsoOn PP.ι χ)
    {Dj : PC.FullSubcategory ⥤ PX.FullSubcategory}
    {Dj' : PC'.FullSubcategory ⥤ PX'.FullSubcategory}
    (νj : PC'.lift (PC.ι ⋙ ΨC) hSpC ⋙ Dj' ⟶ Dj ⋙ PX'.lift (PX.ι ⋙ ΨX) hSpX)
    (lsc : LSfN ≅ Dj ⋙ LSfM) (lsc' : LSfN' ≅ Dj' ⋙ LSfM')
    (H : ∀ M : PC.FullSubcategory, ∃ (e : DhN.obj M.obj ⟶ DhM.obj (Dj.obj M).obj)
      (e' : DhN'.obj (ΨC.obj M.obj) ⟶ DhM'.obj (Dj'.obj ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M)).obj),
      νhN.app M.obj ≫ ΨP.map e =
        e' ≫ DhM'.map (νj.app M).hom ≫ νhM.app (Dj.obj M).obj ∧
      (i₁N.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M)).hom ≫ Rp'.map e' =
        (lsc'.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M)).hom ≫
          (i₁M.hom.app (Dj'.obj ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M))).hom ∧
      (i₂N.inv.app M ≫ lsc.hom.app M).hom = Rp.map e ≫ (i₂M.inv.app (Dj.obj M)).hom)
    (νN : PC'.lift (PC.ι ⋙ ΨC) hSpC ⋙ LSfN' ⟶ LSfN ⋙ Ps'.lift (Ps.ι ⋙ Ψs) hT)
    (hνN : νN = compactSupportExchangeAux Ps'.fullyFaithfulι i₁N i₂N (PC'.liftCompιIso _ hSpC)
        (PP'.liftCompιIso _ hON') (Ps'.liftCompιIso _ hR') (PP.liftCompιIso _ hON)
        (Ps.liftCompιIso _ hR) (Ps'.liftCompιIso _ hT) νhN (invOnSubcategory PP.ι χ hχ))
    (νM : PX'.lift (PX.ι ⋙ ΨX) hSpX ⋙ LSfM' ⟶ LSfM ⋙ Ps'.lift (Ps.ι ⋙ Ψs) hT)
    (hνM : νM = compactSupportExchangeAux Ps'.fullyFaithfulι i₁M i₂M (PX'.liftCompιIso _ hSpX)
        (PP'.liftCompιIso _ hOM') (Ps'.liftCompιIso _ hR') (PP.liftCompιIso _ hOM)
        (Ps.liftCompιIso _ hR) (Ps'.liftCompιIso _ hT) νhM (invOnSubcategory PP.ι χ hχ))
    (M : PC.FullSubcategory) :
    νN.app M ≫ (Ps'.lift (Ps.ι ⋙ Ψs) hT).map (lsc.hom.app M) =
      lsc'.hom.app ((PC'.lift (PC.ι ⋙ ΨC) hSpC).obj M) ≫ LSfM'.map (νj.app M) ≫
        νM.app (Dj.obj M) := by
  subst hνN hνM
  exact compactSupportExchangeAux_lift_comp_app hSpC hSpX hT hON hON' hOM hOM' hR hR' i₁N i₂N
    i₁M i₂M νhN νhM χ hχ νj lsc lsc' H M

/-- `compactSupportExchangeAux_lift_comp_app` for restricted functors `Sp`, `SpX`, `Ts` equal to
the lifts (e.g. definitions unfolding to them) and transformations `νN`, `νM` (heterogeneously)
equal to the shapes `compactSupportExchangeAux …`. -/
lemma compactSupportExchangeAux_lift_comp_app_of_heq {PC : ObjectProperty DC}
    {PC' : ObjectProperty DC'} {PX : ObjectProperty DX} {PX' : ObjectProperty DX'}
    {PP : ObjectProperty DP} {PP' : ObjectProperty DP'} {Ps : ObjectProperty Ds}
    {Ps' : ObjectProperty Ds'} {ΨC : DC ⥤ DC'} {ΨX : DX ⥤ DX'} {ΨP : DP ⥤ DP'}
    {Ψs : Ds ⥤ Ds'} (hSpC : ∀ X, PC' ((PC.ι ⋙ ΨC).obj X)) (hSpX : ∀ X, PX' ((PX.ι ⋙ ΨX).obj X))
    (hT : ∀ X, Ps' ((Ps.ι ⋙ Ψs).obj X)) {DhN : DC ⥤ DP} {DhN' : DC' ⥤ DP'}
    {DhM : DX ⥤ DP} {DhM' : DX' ⥤ DP'} {Rp : DP ⥤ Ds} {Rp' : DP' ⥤ Ds'}
    (hON : ∀ X, PP ((PC.ι ⋙ DhN).obj X)) (hON' : ∀ X, PP' ((PC'.ι ⋙ DhN').obj X))
    (hOM : ∀ X, PP ((PX.ι ⋙ DhM).obj X)) (hOM' : ∀ X, PP' ((PX'.ι ⋙ DhM').obj X))
    (hR : ∀ X, Ps ((PP.ι ⋙ Rp).obj X)) (hR' : ∀ X, Ps' ((PP'.ι ⋙ Rp').obj X))
    {LSfN : PC.FullSubcategory ⥤ Ps.FullSubcategory}
    {LSfN' : PC'.FullSubcategory ⥤ Ps'.FullSubcategory}
    {LSfM : PX.FullSubcategory ⥤ Ps.FullSubcategory}
    {LSfM' : PX'.FullSubcategory ⥤ Ps'.FullSubcategory}
    (i₁N : LSfN' ≅ PP'.lift (PC'.ι ⋙ DhN') hON' ⋙ Ps'.lift (PP'.ι ⋙ Rp') hR')
    (i₂N : LSfN ≅ PP.lift (PC.ι ⋙ DhN) hON ⋙ Ps.lift (PP.ι ⋙ Rp) hR)
    (i₁M : LSfM' ≅ PP'.lift (PX'.ι ⋙ DhM') hOM' ⋙ Ps'.lift (PP'.ι ⋙ Rp') hR')
    (i₂M : LSfM ≅ PP.lift (PX.ι ⋙ DhM) hOM ⋙ Ps.lift (PP.ι ⋙ Rp) hR)
    (νhN : ΨC ⋙ DhN' ⟶ DhN ⋙ ΨP) (νhM : ΨX ⋙ DhM' ⟶ DhM ⋙ ΨP)
    (χ : Rp ⋙ Ψs ⟶ ΨP ⋙ Rp') (hχ : IsIsoOn PP.ι χ)
    {Dj : PC.FullSubcategory ⥤ PX.FullSubcategory}
    {Dj' : PC'.FullSubcategory ⥤ PX'.FullSubcategory}
    (lsc : LSfN ≅ Dj ⋙ LSfM) (lsc' : LSfN' ≅ Dj' ⋙ LSfM')
    {Sp : PC.FullSubcategory ⥤ PC'.FullSubcategory}
    {SpX : PX.FullSubcategory ⥤ PX'.FullSubcategory}
    {Ts : Ps.FullSubcategory ⥤ Ps'.FullSubcategory}
    (eSp : PC'.lift (PC.ι ⋙ ΨC) hSpC = Sp) (eSpX : PX'.lift (PX.ι ⋙ ΨX) hSpX = SpX)
    (eTs : Ps'.lift (Ps.ι ⋙ Ψs) hT = Ts) (νj : Sp ⋙ Dj' ⟶ Dj ⋙ SpX)
    (νN : Sp ⋙ LSfN' ⟶ LSfN ⋙ Ts)
    (hνN : HEq νN (compactSupportExchangeAux Ps'.fullyFaithfulι i₁N i₂N
        (PC'.liftCompιIso _ hSpC) (PP'.liftCompιIso _ hON') (Ps'.liftCompιIso _ hR')
        (PP.liftCompιIso _ hON) (Ps.liftCompιIso _ hR) (Ps'.liftCompιIso _ hT) νhN
        (invOnSubcategory PP.ι χ hχ)))
    (νM : SpX ⋙ LSfM' ⟶ LSfM ⋙ Ts)
    (hνM : HEq νM (compactSupportExchangeAux Ps'.fullyFaithfulι i₁M i₂M
        (PX'.liftCompιIso _ hSpX) (PP'.liftCompιIso _ hOM') (Ps'.liftCompιIso _ hR')
        (PP.liftCompιIso _ hOM) (Ps.liftCompιIso _ hR) (Ps'.liftCompιIso _ hT) νhM
        (invOnSubcategory PP.ι χ hχ)))
    (H : ∀ M : PC.FullSubcategory, ∃ (e : DhN.obj M.obj ⟶ DhM.obj (Dj.obj M).obj)
      (e' : DhN'.obj (Sp.obj M).obj ⟶ DhM'.obj (Dj'.obj (Sp.obj M)).obj),
      νhN.app M.obj ≫ ΨP.map e = DhN'.map (eqToHom (congrArg (fun F ↦ (F.obj M).obj) eSp)) ≫
        e' ≫ DhM'.map (νj.app M).hom ≫
          DhM'.map (eqToHom (congrArg (fun F ↦ (F.obj (Dj.obj M)).obj) eSpX.symm)) ≫
          νhM.app (Dj.obj M).obj ∧
      (i₁N.hom.app (Sp.obj M)).hom ≫ Rp'.map e' =
        (lsc'.hom.app (Sp.obj M)).hom ≫ (i₁M.hom.app (Dj'.obj (Sp.obj M))).hom ∧
      (i₂N.inv.app M ≫ lsc.hom.app M).hom = Rp.map e ≫ (i₂M.inv.app (Dj.obj M)).hom)
    (M : PC.FullSubcategory) :
    νN.app M ≫ Ts.map (lsc.hom.app M) =
      lsc'.hom.app (Sp.obj M) ≫ LSfM'.map (νj.app M) ≫ νM.app (Dj.obj M) := by
  subst eSp eSpX eTs
  rw [eq_of_heq hνN, eq_of_heq hνM]
  refine compactSupportExchangeAux_lift_comp_app hSpC hSpX hT hON hON' hOM hOM' hR hR' i₁N i₂N
    i₁M i₂M νhN νhM χ hχ νj lsc lsc' (fun M ↦ ?_) M
  obtain ⟨e, e', h1, h2, h3⟩ := H M
  exact ⟨e, e', by simpa using h1, h2, h3⟩

end Shape

end AlgebraicGeometry.ProEtale.CondensedRing
