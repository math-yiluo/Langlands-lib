/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroCoverDatum
public import WeilConjectures.ConstructibleSheaf.SylowGaloisCoverTrivializing
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalizationRamification
public import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverPullback
public import WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions
public import WeilConjectures.ConstructibleSheaf.DenseOpenUnit
import WeilConjectures.ConstructibleSheaf.LisseModuleTrivializingTorsor
import WeilConjectures.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient
import Mathlib.GroupTheory.Sylow

/-!

# Existence of the cover datum

This file assembles the ingredients of blueprint `lemma-tangent-cones-on-cover` (i) into a
cover datum `AlgebraicGeometry.Etale.CurveLocalModel.CoverDatum`:

* `AlgebraicGeometry.Scheme.exists_sylow_galoisCover_trivializing_connected`: a version of
  `AlgebraicGeometry.Scheme.exists_sylow_galoisCover_trivializing` recording that the total
  space of the `ℓ`-group Galois cover is connected;
* `CategoryTheory.Functor.FullyFaithful.homologicalComplexOfIso`: a complex whose terms lie in
  the essential image of a fully faithful additive functor lies in the essential image of the
  induced functor on complexes;
* `AlgebraicGeometry.Scheme.exists_constantComplex_iso`: on a connected scheme, a bounded complex
  whose terms are constant sheaves with finite values is isomorphic, as a complex, to the constant
  complex on a bounded complex of finite modules.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

/-- A version of `AlgebraicGeometry.Scheme.exists_sylow_galoisCover_trivializing` recording that
the total space of the `ℓ`-group Galois cover is connected. -/
theorem Scheme.exists_sylow_galoisCover_trivializing_connected {U : Scheme.{u}}
    [ConnectedSpace U] (ℓ : ℕ) [Fact ℓ.Prime] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {ι : Type} [Finite ι] (F : ι → Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ i, IsFiniteLocallyConstantSheaf (F i)] :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v) (_ : ConnectedSpace V)
      (d : ℕ), ¬ ℓ ∣ d ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = d) ∧
      ∃ (P : Type (u + 1)) (_ : Group P) (_ : Finite P) (_ : IsPGroup ℓ P)
        (c : Scheme.GaloisCover P V) (_ : ConnectedSpace c.P), ∀ i,
          ∃ (M : ModuleCat.{u + 1} Λ) (_ : Finite M),
          Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj ((v)^*[ModuleCat.{u + 1} Λ].obj (F i)) ≅
            (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  obtain ⟨Q, hQ, hQfin, c, hc, htriv⟩ :=
    IsFiniteLocallyConstantSheaf.exists_galoisCover_trivializing F
  let H : Sylow ℓ Q := Classical.choice inferInstance
  obtain ⟨V, v, hvfin, hvet, hV, hcard, cH, hcH, e, he⟩ :=
    c.exists_connected_subgroup_quotient Q H.toSubgroup
  let C := ModuleCat.{u + 1} Λ
  refine ⟨V, v, hvfin, hvet, hV, H.index, H.not_dvd_index, hcard, ULift.{u + 1} H.toSubgroup,
    inferInstance, inferInstance, H.isPGroup'.of_equiv MulEquiv.ulift.symm, cH, hcH, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨α⟩⟩ := htriv i
  exact ⟨M, hM, ⟨((upperStarComp C cH.π v).app (F i)).symm ≪≫
    (upperStarComp C e.hom c.π (cH.π ≫ v) he.symm).app (F i) ≪≫
    ((e.hom)^*[C]).mapIso α ≪≫ (Scheme.upperStarConstantSheafIso C e.hom).app M⟩⟩

end AlgebraicGeometry

namespace CategoryTheory.Functor.FullyFaithful

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} [F.Additive] (hF : F.FullyFaithful) {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex D c) (M : ι → C) (α : ∀ i, K.X i ≅ F.obj (M i))

/-- For a fully faithful additive functor `F` and a complex `K` with `K_i ≅ F(M_i)`, the complex
with terms `M_i` whose differentials are the preimages of those of `K`. -/
@[simps]
noncomputable def homologicalComplexOfIso : HomologicalComplex C c where
  X := M
  d i j := hF.preimage ((α i).inv ≫ K.d i j ≫ (α j).hom)
  shape i j h := hF.map_injective (by
    rw [hF.map_preimage, K.shape i j h]
    simp)
  d_comp_d' i j k _ _ := hF.map_injective (by simp)

/-- The isomorphism `K ≅ F(homologicalComplexOfIso hF K M α)`. -/
noncomputable def isoMapHomologicalComplexOfIso :
    K ≅ (F.mapHomologicalComplex c).obj (hF.homologicalComplexOfIso K M α) :=
  HomologicalComplex.Hom.isoOfComponents α (fun i j _ ↦ by simp)

end CategoryTheory.Functor.FullyFaithful

namespace AlgebraicGeometry.Scheme

/-- **Constant complexes on a connected scheme.** On a connected scheme, a complex of sheaves of
`Λ`-modules vanishing outside `[a, b]` whose terms in `[a, b]` are constant sheaves with finite
values is isomorphic, as a complex, to the constant complex on a bounded complex of finite
`Λ`-modules: the constant sheaf functor is fully faithful. -/
theorem exists_constantComplex_iso {Z : Scheme.{u}} [ConnectedSpace Z] {Λ : Type (u + 1)}
    [CommRing Λ] (K : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (a b : ℤ) (hK : ∀ q : ℤ, q < a ∨ b < q → IsZero (K.X q))
    (hM : ∀ q : ℤ, a ≤ q → q ≤ b → ∃ (M : ModuleCat.{u + 1} Λ) (_ : Finite M),
      Nonempty (K.X q ≅ (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    ∃ (Cx : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (a b : ℤ) (_ : Cx.IsStrictlyGE a)
      (_ : Cx.IsStrictlyLE b) (_ : ∀ n, Finite (Cx.X n)),
      Nonempty (K ≅
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Cx) := by
  classical
  let F := constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have hex (q : ℤ) : ∃ (M : ModuleCat.{u + 1} Λ) (_ : Finite M), Nonempty (K.X q ≅ F.obj M) := by
    by_cases h : a ≤ q ∧ q ≤ b
    · exact hM q h.1 h.2
    · refine ⟨ModuleCat.of Λ PUnit, inferInstance, ⟨(hK q (by omega)).iso ?_⟩⟩
      exact F.map_isZero (ModuleCat.isZero_of_subsingleton _)
  choose M hMf α using hex
  let hF := Scheme.fullyFaithfulModuleConstantSheaf Z Λ
  have hz (q : ℤ) (hq : q < a ∨ b < q) : IsZero (M q) := by
    rw [IsZero.iff_id_eq_zero]
    refine hF.map_injective ?_
    rw [F.map_id, F.map_zero]
    exact ((hK q hq).of_iso (α q).some.symm).eq_of_src _ _
  refine ⟨hF.homologicalComplexOfIso K M (fun q ↦ (α q).some), a, b, ?_, ?_, hMf,
    ⟨hF.isoMapHomologicalComplexOfIso K M _⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun q hq ↦ hz q (Or.inl hq)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun q hq ↦ hz q (Or.inr hq)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

omit [IsAlgClosed k] in
/-- The point `y` of the model has an irreducible affine open neighbourhood. -/
lemma exists_isAffineOpen_irreducibleSpace :
    ∃ U : M.X.Opens, IsAffineOpen U ∧ IrreducibleSpace U ∧
      M.y.base (default : Spec (.of k)) ∈ U := by
  have : Smooth M.f := SmoothOfRelativeDimension.smooth 1 M.f
  have : IsRegular M.X := IsRegular.of_smooth M.f
  have : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.f
  obtain ⟨O, hyO, hO⟩ := exists_isOpen_irreducibleSpace_of_isDomain_stalk
    (fun x ↦ @IsRegularLocalRing.isDomain _ _ (IsRegular.isRegularLocalRing_stalk x))
    (M.y.base default)
  obtain ⟨U, hU, hyU, hUO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp M.X.isBasis_affineOpens hyO
  have hOirr : IsIrreducible (O : Set M.X) := isIrreducible_iff_irreducibleSpace.mpr hO
  have hUirr : IsIrreducible (U : Set M.X) :=
    ⟨⟨_, hyU⟩, hOirr.2.open_subset U.isOpen hUO⟩
  exact ⟨U, hU, Subtype.irreducibleSpace hUirr, hyU⟩

omit [IsAlgClosed k] in
/-- A closed point `y` of the model has a strict generalization. -/
lemma exists_specializes_ne :
    ∃ z : M.X, z ⤳ M.y.base (default : Spec (.of k)) ∧ z ≠ M.y.base default := by
  have h := ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one M.f M.isClosed_y
  rw [ringKrullDim_stalk_eq_coheight] at h
  have hne : Order.coheight (M.y.base default) ≠ 0 := by
    intro h0
    rw [h0] at h
    exact absurd h (by decide)
  obtain ⟨z, hz⟩ := not_isMax_iff.mp (mt Order.coheight_eq_zero.mpr hne)
  exact ⟨z, hz.le, hz.ne'⟩

/-- **Existence of the cover datum** (blueprint `lemma-tangent-cones-on-cover` (i), first
half). -/
theorem nonempty_coverDatum (ℓ : ℕ) [Fact ℓ.Prime] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (PL PK : CochainComplex (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hPL : ∃ a b, IsBoundedFlatComplex Λ a b PL) (hPK : ∃ a b, IsBoundedFlatComplex Λ a b PK)
    (hcL : ∀ q : ℤ, IsConstructibleSheaf (PL.X q)) (hcK : ∀ q : ℤ, IsConstructibleSheaf (PK.X q)) :
    Nonempty (M.CoverDatum ℓ PL PK) := by
  classical
  let A := ModuleCat.{u + 1} Λ
  obtain ⟨aL, bL, hzL, -⟩ := hPL
  obtain ⟨aK, bK, hzK, -⟩ := hPK
  have : Smooth M.f := SmoothOfRelativeDimension.smooth 1 M.f
  obtain ⟨U, hUaff, hUirr, hyU⟩ := M.exists_isAffineOpen_irreducibleSpace
  have : SmoothOfRelativeDimension 1 (U.ι ≫ M.f) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.ι ≫ M.f))
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ M.f)
  have : IsAffine U := hUaff
  have : IsNoetherian U := {}
  have : TopologicalSpace.NoetherianSpace U := inferInstance
  have hdim : topologicalKrullDim U ≤ 1 := by
    exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension (U.ι ≫ M.f) 1
  -- the point `y` of `U`
  let x : U := ⟨M.y.base default, hyU⟩
  have hx : IsClosed ({x} : Set U) := by
    have : ({x} : Set U) = Subtype.val ⁻¹' {M.y.base default} := by
      ext z
      rw [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
    rw [this]
    exact M.isClosed_y.preimage continuous_subtype_val
  -- the terms of the complexes, lisse on a punctured neighbourhood
  let F : Finset.Icc aL bL ⊕ Finset.Icc aK bK → Sheaf U.toScheme.smallEtaleTopology A :=
    Sum.elim (fun q ↦ (U.ι)^*[A].obj (PL.X q)) (fun q ↦ (U.ι)^*[A].obj (PK.X q))
  have (i : _) : IsConstructibleSheaf (F i) := by
    rcases i with q | q
    · exact IsConstructibleSheaf.upperStar _ _
    · exact IsConstructibleSheaf.upperStar _ _
  obtain ⟨W₀, hxW₀, hW₀⟩ := exists_isFiniteLocallyConstantSheaf_punctured hdim hx F
  -- the punctured neighbourhood `U' = W ∖ y` of `y` in `X`
  let W : M.X.Opens := U.ι ''ᵁ W₀
  have hyW : M.y.base default ∈ W := ⟨x, hxW₀, rfl⟩
  let U' := puncturedOpens W _ M.isClosed_y
  have hU'U : U' ≤ U := fun z hz ↦ U.ι_image_le W₀ hz.1
  have hrange : Set.range U'.ι.base ⊆ Set.range ((puncturedOpens W₀ x hx).ι ≫ U.ι).base := by
    rw [Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι]
    rintro z ⟨⟨w, hw, rfl⟩, hzy⟩
    refine ⟨w, ⟨hw, fun h ↦ hzy ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff.mp h]
    rfl
  obtain ⟨z, hzy, hzne⟩ := M.exists_specializes_ne
  have : Nonempty U' := ⟨⟨z, hzy.mem_open W.isOpen hyW, hzne⟩⟩
  have : IrreducibleSpace U' := by
    have hUs : IsIrreducible (U : Set M.X) := isIrreducible_iff_irreducibleSpace.mpr hUirr
    exact Subtype.irreducibleSpace
      ⟨⟨z, hzy.mem_open W.isOpen hyW, hzne⟩, hUs.2.open_subset U'.isOpen hU'U⟩
  -- the terms restricted to `U'` are finite locally constant
  let G : Finset.Icc aL bL ⊕ Finset.Icc aK bK → Sheaf U'.toScheme.smallEtaleTopology A :=
    Sum.elim (fun q ↦ (U'.ι)^*[A].obj (PL.X q)) (fun q ↦ (U'.ι)^*[A].obj (PK.X q))
  have (i : _) : IsFiniteLocallyConstantSheaf (G i) := by
    rcases i with q | q
    · have : IsFiniteLocallyConstantSheaf
          (((U.ι)^*[A] ⋙ ((puncturedOpens W₀ x hx).ι)^*[A]).obj (PL.X q)) := hW₀ (.inl q)
      have : IsFiniteLocallyConstantSheaf
          (((puncturedOpens W₀ x hx).ι ≫ U.ι)^*[A].obj (PL.X q)) :=
        IsFiniteLocallyConstantSheaf.of_iso
          ((upperStarComp A (puncturedOpens W₀ x hx).ι U.ι).app (PL.X q)).symm
      exact IsFiniteLocallyConstantSheaf.upperStar_of_range_subset _ _ hrange (PL.X q)
    · have : IsFiniteLocallyConstantSheaf
          (((U.ι)^*[A] ⋙ ((puncturedOpens W₀ x hx).ι)^*[A]).obj (PK.X q)) := hW₀ (.inr q)
      have : IsFiniteLocallyConstantSheaf
          (((puncturedOpens W₀ x hx).ι ≫ U.ι)^*[A].obj (PK.X q)) :=
        IsFiniteLocallyConstantSheaf.of_iso
          ((upperStarComp A (puncturedOpens W₀ x hx).ι U.ι).app (PK.X q)).symm
      exact IsFiniteLocallyConstantSheaf.upperStar_of_range_subset _ _ hrange (PK.X q)
  obtain ⟨V, v, hvfin, hvet, hVconn, d, hℓd, hd, P, hP, hPfin, hPℓ, c, hcconn, htriv⟩ :=
    Scheme.exists_sylow_galoisCover_trivializing_connected ℓ G
  obtain ⟨C, pU, hpU, hsm, cpt, hc, e, he1, heℓ, hram, j, hj, hjp, hjrange⟩ :=
    exists_finite_smooth_cover_not_dvd_ramificationIdx M.f M.y M.y_comp hUaff hyU hU'U v ℓ d hd
      hℓd
  -- `p : C ⟶ X` and the identification `V ≅ p⁻¹(U')`
  let p := pU ≫ U.ι
  have hpre : Set.range j.base = Set.range (p ⁻¹ᵁ U').ι.base := by
    rw [hjrange, Opens.range_ι]
    ext w
    simp only [Set.mem_preimage, Set.mem_range, p, SetLike.mem_coe, Scheme.Hom.mem_preimage,
      Scheme.Hom.comp_apply, Opens.ι_apply]
    constructor
    · rintro ⟨w', hw'⟩
      rw [← hw', Scheme.homOfLE_apply]
      exact w'.2
    · intro h
      exact ⟨⟨_, h⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  let eV : V ≅ (p ⁻¹ᵁ U').toScheme := IsOpenImmersion.isoOfRangeEq j (p ⁻¹ᵁ U').ι hpre
  have hres : eV.hom ≫ p ∣_ U' = v := by
    rw [← cancel_mono U'.ι, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, reassoc_of% hjp, Scheme.homOfLE_ι]
  have hetale : Etale (p ∣_ U') := by
    have h : p ∣_ U' = eV.inv ≫ v := by rw [← hres, Iso.inv_hom_id_assoc]
    rw [h]
    infer_instance
  -- the Galois cover of `p⁻¹(U')`
  let gal := c.pullback eV.inv
  have : ConnectedSpace gal.P :=
    (Scheme.homeoOfIso (asIso (pullback.fst c.π eV.inv)).symm).surjective.connectedSpace
      (Scheme.homeoOfIso _).continuous
  have hgal : gal.π ≫ (p ⁻¹ᵁ U').ι ≫ p = pullback.fst c.π eV.inv ≫ c.π ≫ v ≫ U'.ι := by
    have h : (p ⁻¹ᵁ U').ι ≫ p = eV.inv ≫ v ≫ U'.ι := by
      rw [← morphismRestrict_ι, ← hres, Category.assoc, Iso.inv_hom_id_assoc]
    rw [h]
    exact (pullback.condition_assoc _).symm
  have key (Q : CochainComplex (Sheaf M.X.smallEtaleTopology A) ℤ) (a b : ℤ)
      (hz : ∀ q : ℤ, q < a ∨ b < q → IsZero (Q.X q))
      (ht : ∀ q : ℤ, a ≤ q → q ≤ b → ∃ (N : ModuleCat.{u + 1} Λ) (_ : Finite N),
        Nonempty ((c.π)^*[A].obj ((v)^*[A].obj ((U'.ι)^*[A].obj (Q.X q))) ≅
          (constantSheaf c.P.smallEtaleTopology A).obj N)) :
      ∃ (Cx : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (a b : ℤ) (_ : Cx.IsStrictlyGE a)
        (_ : Cx.IsStrictlyLE b) (_ : ∀ n, Finite (Cx.X n)),
        Nonempty (((upperStar A (gal.π ≫ (p ⁻¹ᵁ U').ι ≫ p)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Q ≅
          ((constantSheaf gal.P.smallEtaleTopology A).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Cx) := by
    refine exists_constantComplex_iso _ a b (fun q hq ↦ ?_) (fun q h1 h2 ↦ ?_)
    · exact (upperStar A (gal.π ≫ (p ⁻¹ᵁ U').ι ≫ p)).map_isZero (hz q hq)
    · obtain ⟨N, hN, ⟨α⟩⟩ := ht q h1 h2
      exact ⟨N, hN, ⟨(upperStarComp A (pullback.fst c.π eV.inv) (c.π ≫ v ≫ U'.ι) _ hgal).app
        (Q.X q) ≪≫ (pullback.fst c.π eV.inv)^*[A].mapIso
          ((upperStarComp A c.π (v ≫ U'.ι)).app _ ≪≫
            (c.π)^*[A].mapIso ((upperStarComp A v U'.ι).app _) ≪≫ α) ≪≫
        (Scheme.upperStarConstantSheafIso A (pullback.fst c.π eV.inv)).app N⟩⟩
  exact ⟨{
    C := C
    fC := pU ≫ U.ι ≫ M.f
    smoothOfRelativeDimension := hsm
    p := p
    U := U
    mem_U := hyU
    pU := pU
    isFinite := hpU
    pU_ι := rfl
    p_comp := Category.assoc _ _ _
    c := cpt
    c_comp := hc
    e := e
    one_le_e := he1
    not_dvd_e := heℓ
    ramification := hram
    W := W
    mem_W := hyW
    etale := hetale
    G := P
    isPGroup := hPℓ
    galois := gal
    trivializes := by
      rintro Q (rfl | rfl)
      · exact key _ aL bL hzL fun q h1 h2 ↦ htriv (.inl ⟨q, Finset.mem_Icc.2 ⟨h1, h2⟩⟩)
      · exact key _ aK bK hzK fun q h1 h2 ↦ htriv (.inr ⟨q, Finset.mem_Icc.2 ⟨h1, h2⟩⟩) }⟩

end AlgebraicGeometry.Etale.CurveLocalModel
