/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.InternalHom

/-!
# Extensions of constructible `Λ`-adic sheaves

This is the counterpart, for a coefficient field `Λ` with an ultrametric norm (the case of
interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.Extension`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

An epimorphism `q : P ⟶ Q` of sheaves of `Λ_X`-modules is locally split over a section
`Λ_X ⟶ Q`: there is a pro-étale cover over each member `g : W ⟶ X` of which the section lifts to
`g^* P` (`AlgebraicGeometry.ProEtale.exists_cover_field_lift`). The underlying section lifts on a
covering sieve because `q` is locally surjective, and a section over the terminal object of
`W.ProEt` is a map out of the unit sheaf (`AlgebraicGeometry.ProEtale.fieldUnitSheafLift`); the unit
comparison of the pullback is computed through the restriction to the slice site.

Applied to a basis of `Λⁿ`, an extension of `Λⁿ` by a lisse sheaf splits locally, so
extensions of lisse sheaves are lisse
(`AlgebraicGeometry.ProEtale.IsFieldLisseSheaf.of_shortExact`).
Refining stratifications, extensions of constructible sheaves are constructible
(`AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.of_shortExact`), i.e.
`(fieldConstructibleSheaf Λ X).IsClosedUnderExtensions`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

universe u

open scoped Obj


namespace AlgebraicGeometry.ProEtale

variable {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]

section

variable {W : Scheme.{u}}

/-- The map out of the unit presheaf sending `1` to a section over the terminal object. -/
noncomputable def fieldUnitPresheafLift {G : (W.ProEt)ᵒᵖ ⥤ FieldCoefficients.{u} Λ}
    (x : G.obj (op (⊤_ W.ProEt))) :
    𝟙_ ((W.ProEt)ᵒᵖ ⥤ FieldCoefficients.{u} Λ) ⟶ G where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (G.map (terminal.from U.unop).op x))
  naturality U U' f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
    change ULift.{u + 1} Λ at r
    change (r : ULift Λ) • G.map (terminal.from U'.unop).op x =
      G.map f (r • G.map (terminal.from U.unop).op x)
    rw [map_smul, ← ConcreteCategory.comp_apply, ← G.map_comp,
      show (terminal.from (unop U)).op ≫ f = (terminal.from (unop U')).op from
        Quiver.Hom.unop_inj (terminal.hom_ext _ _)]

omit [IsUltrametricDist Λ] in
lemma fieldUnitPresheafLift_app_one {G : (W.ProEt)ᵒᵖ ⥤ FieldCoefficients.{u} Λ}
    (x : G.obj (op (⊤_ W.ProEt))) :
    (fieldUnitPresheafLift x).app (op (⊤_ W.ProEt)) (1 : ULift.{u + 1} Λ) = x := by
  change (1 : ULift Λ) • G.map (terminal.from _).op x = x
  rw [one_smul, terminal.hom_ext (terminal.from (⊤_ W.ProEt)) (𝟙 _), op_id, G.map_id]
  rfl

omit [IsUltrametricDist Λ] in
lemma fieldUnitPresheaf_hom_ext {G : (W.ProEt)ᵒᵖ ⥤ FieldCoefficients.{u} Λ}
    {a b : 𝟙_ ((W.ProEt)ᵒᵖ ⥤ FieldCoefficients.{u} Λ) ⟶ G}
    (h : a.app (op (⊤_ W.ProEt)) (1 : ULift.{u + 1} Λ) =
      b.app (op (⊤_ W.ProEt)) (1 : ULift.{u + 1} Λ)) : a = b := by
  have key (c : 𝟙_ ((W.ProEt)ᵒᵖ ⥤ FieldCoefficients.{u} Λ) ⟶ G) :
      c = fieldUnitPresheafLift (c.app (op (⊤_ W.ProEt)) (1 : ULift.{u + 1} Λ)) := by
    ext U : 2
    refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
    revert r
    change ∀ r : ULift.{u + 1} Λ, c.app U r = r • G.map (terminal.from U.unop).op
      (c.app (op (⊤_ W.ProEt)) (1 : ULift.{u + 1} Λ))
    intro r
    rw [← ConcreteCategory.comp_apply, ← c.naturality]
    change c.app U r = r • c.app U (1 : ULift.{u + 1} Λ)
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [key a, key b, h]

end

section

variable {W : Scheme.{u}}



/-- The map out of the unit sheaf sending `1` to a section over the terminal object. -/
noncomputable def fieldUnitSheafLift {F : Sheaf (Scheme.ProEt.topology W) (FieldCoefficients.{u} Λ)}
    (x : F.obj.obj (op (⊤_ W.ProEt))) : 𝟙_ _ ⟶ F :=
  inv (η (presheafToSheaf (Scheme.ProEt.topology W) (FieldCoefficients.{u} Λ))) ≫
    ((sheafificationAdjunction _ _).homEquiv _ _).symm (fieldUnitPresheafLift x)

omit [IsUltrametricDist Λ] in
lemma ε_comp_fieldUnitSheafLift {F : Sheaf (Scheme.ProEt.topology W) (FieldCoefficients.{u} Λ)}
    (x : F.obj.obj (op (⊤_ W.ProEt))) :
    ε (sheafToPresheaf _ _) ≫ (sheafToPresheaf _ _).map (fieldUnitSheafLift x) =
      fieldUnitPresheafLift x := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology W) (FieldCoefficients.{u} Λ)).homEquiv
    _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm]
  have : ((sheafificationAdjunction (Scheme.ProEt.topology W)
      (FieldCoefficients.{u} Λ)).homEquiv _ _).symm (ε (sheafToPresheaf _ _)) =
        η (presheafToSheaf (Scheme.ProEt.topology W) (FieldCoefficients.{u} Λ)) :=
    Equiv.symm_apply_apply _ _
  rw [this, fieldUnitSheafLift, IsIso.hom_inv_id_assoc]

end

section



variable {V : Scheme.{u}}

omit [IsUltrametricDist Λ] in
/-- An epimorphism of pro-étale sheaves of `Λ`-modules is locally surjective. -/
lemma isLocallySurjective_of_epi_field
    {P Q : Sheaf (Scheme.ProEt.topology V) (FieldCoefficients.{u} Λ)}
    (q : P ⟶ Q) [Epi q] : Sheaf.IsLocallySurjective q :=
  (Sheaf.isLocallySurjective_iff_epi' (φ := q)).2 inferInstance

omit [IsUltrametricDist Λ] in
/-- **Local lifting of a section along an epimorphism.** A map `τ : 𝟙 ⟶ Q` lifts along an
epimorphism `q : P ⟶ Q` after restriction to the members of a pro-étale cover. -/
lemma exists_cover_unit_lift_field {P Q : Sheaf (Scheme.ProEt.topology V) (FieldCoefficients.{u} Λ)}
    (q : P ⟶ Q) [Epi q] (τ : 𝟙_ _ ⟶ Q) :
    ∃ R ∈ Scheme.proetalePrecoverage V, ∀ ⦃W : Scheme.{u}⦄ (g : W ⟶ V), R g →
      ∃ (hg : WeaklyEtale g) (σ : 𝟙_ _ ⟶
        ((MorphismProperty.Over.map ⊤ hg).sheafPushforwardContinuous
          (FieldCoefficients.{u} Λ) (Scheme.ProEt.topology W) (Scheme.ProEt.topology V)).obj P),
        σ ≫ ((MorphismProperty.Over.map ⊤ hg).sheafPushforwardContinuous
          (FieldCoefficients.{u} Λ) (Scheme.ProEt.topology W) (Scheme.ProEt.topology V)).map q =
        ε _ ≫ ((MorphismProperty.Over.map ⊤ hg).sheafPushforwardContinuous
          (FieldCoefficients.{u} Λ) (Scheme.ProEt.topology W) (Scheme.ProEt.topology V)).map τ := by
  let T : V.ProEt := Scheme.ProEt.mk (𝟙 V)
  let y : Q.obj.obj (op T) :=
    (ε (sheafToPresheaf _ _) ≫ (sheafToPresheaf _ _).map τ).app (op T)
      (1 : ULift.{u + 1} Λ)
  have hq : Sheaf.IsLocallySurjective q := isLocallySurjective_of_epi_field q
  have hS := Presheaf.imageSieve_mem (Scheme.ProEt.topology V) q.hom (U := op T) y
  rw [Scheme.ProEt.mem_topology_iff] at hS
  obtain ⟨R, hR, hle⟩ := hS
  obtain ⟨ι, Z, φ, rfl⟩ := R.exists_eq_ofArrows
  have hR' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (φ i).left) ∈
      Scheme.proetalePrecoverage V := by
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hR
    exact hR
  refine ⟨_, hR', ?_⟩
  rintro _ _ ⟨i⟩
  have hw := Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR' (.mk i)
  obtain ⟨x, hx⟩ := hle _ (φ i) (Presieve.ofArrows.mk i)
  let TW := ⊤_ (Z i).left.ProEt
  let k : (MorphismProperty.Over.map ⊤ hw).obj TW ⟶ Z i :=
    MorphismProperty.Over.homMk TW.hom (by
      have := MorphismProperty.Over.w (φ i)
      rw [← this]
      exact congrArg (TW.hom ≫ ·) (Category.comp_id _))
  refine ⟨hw, fieldUnitSheafLift (P.obj.map k.op x), ?_⟩
  apply Sheaf.hom_ext_of_ε_comp
  apply fieldUnitPresheaf_hom_ext
  rw [Functor.map_comp, reassoc_of% ε_comp_fieldUnitSheafLift, Functor.map_comp, NatTrans.comp_app,
    ConcreteCategory.comp_apply, fieldUnitPresheafLift_app_one]
  simp only [NatTrans.comp_app]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
  change q.hom.app _ (P.obj.map k.op x) = τ.hom.app _
    ((ε (sheafToPresheaf (Scheme.ProEt.topology V) (FieldCoefficients.{u} Λ))).app _
      (1 : ULift.{u + 1} Λ))
  rw [NatTrans.naturality_apply, hx, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  simp only [y]
  erw [← NatTrans.naturality_apply (ε (sheafToPresheaf _ _) ≫ (sheafToPresheaf _ _).map τ)]
  rfl

end

section

variable {V : Scheme.{u}}

/-- **Local lifting of a section along an epimorphism of `Λ_V`-modules.** -/
lemma exists_cover_field_lift {P Q : FieldSheaf Λ V} (q : P ⟶ Q) [Epi q]
    (t : FieldSheaf.unit Λ V ⟶ Q) :
    ∃ R ∈ Scheme.proetalePrecoverage V, ∀ ⦃W : Scheme.{u}⦄ (g : W ⟶ V), R g →
      WeaklyEtale g ∧ ∃ s : FieldSheaf.unit Λ W ⟶ (g)^*ᶠ[Λ].obj P,
        s ≫ (g)^*ᶠ[Λ].map q = (fieldUpperStarUnitIso Λ g).inv ≫ (g)^*ᶠ[Λ].map t := by
  have : Epi q.hom := (Mod.forget _).map_epi q
  obtain ⟨R, hR, h⟩ :=
    exists_cover_unit_lift_field q.hom ((MonObj.one : 𝟙_ _ ⟶ fieldConstantSheaf Λ V) ≫ t.hom)
  refine ⟨R, hR, fun W g hg ↦ ?_⟩
  obtain ⟨hw, σ, hσ⟩ := h g hg
  let e := upperStarIsoSheafPushforward (FieldCoefficients.{u} Λ) g hw
  refine ⟨hw, Mod.regularLift ((g)^*ᶠ[Λ].obj P) (σ ≫ e.inv.app P.X), ?_⟩
  apply Mod.regular_hom_ext
  have h1 : (Mod.regularLift ((g)^*ᶠ[Λ].obj P) (σ ≫ e.inv.app P.X) ≫ (g)^*ᶠ[Λ].map q).hom =
      (Mod.regularLift ((g)^*ᶠ[Λ].obj P) (σ ≫ e.inv.app P.X)).hom ≫
        (g)^*[FieldCoefficients.{u} Λ].map q.hom :=
    rfl
  have h2 : ((fieldUpperStarUnitIso Λ g).inv ≫ (g)^*ᶠ[Λ].map t).hom =
      (fieldUpperStarUnitIso Λ g).inv.hom ≫ (g)^*[FieldCoefficients.{u} Λ].map t.hom :=
    rfl
  erw [h1, h2, ← Category.assoc, Mod.one_comp_regularLift]
  rw [Category.assoc, ← e.inv.naturality, reassoc_of% hσ, e.inv.naturality]
  have hε : ε ((MorphismProperty.Over.map ⊤ hw).sheafPushforwardContinuous (FieldCoefficients Λ)
      (Scheme.ProEt.topology W) (Scheme.ProEt.topology V)) ≫ e.inv.app (𝟙_ _) =
        ε (g)^*[FieldCoefficients.{u} Λ] := by
    rw [← NatTrans.IsMonoidal.unit (τ := e.hom), Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  rw [← Category.assoc, hε, Functor.map_comp]
  simp only [fieldUpperStarUnitIso, Mod.regularIsoOfIsIso_inv_hom]
  have h3 : (MonObj.one : 𝟙_ _ ⟶ fieldConstantSheaf Λ W) ≫ fieldUpperStarRingIso (Λ := Λ) g =
      ε (g)^*[FieldCoefficients.{u} Λ] ≫
        (g)^*[FieldCoefficients.{u} Λ].map (MonObj.one : 𝟙_ _ ⟶ fieldConstantSheaf Λ V) := by
    have : IsMonHom (fieldUpperStarRingIso (Λ := Λ) g) :=
      inferInstanceAs (IsMonHom (inv (((upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ)
        g).homEquiv _ _).symm (fieldConstantSheafToLowerStar Λ g))))
    rw [IsMonHom.one_hom]
    rfl
  exact ((reassoc_of% h3) _).symm


end

section

attribute [local instance] Abelian.hasFiniteBiproducts
  preservesBinaryBiproducts_of_preservesBiproducts

variable {X : Scheme.{u}}

/-- **Being lisse is local**: a sheaf whose pullbacks along the members of a pro-étale cover are
lisse is lisse. -/
lemma IsFieldLisseSheaf.of_presieve {F : FieldSheaf Λ X} (R : Presieve X)
    (hR : R ∈ Scheme.proetalePrecoverage X)
    (h : ∀ ⦃V : Scheme.{u}⦄ (f : V ⟶ X), R f → IsFieldLisseSheaf ((f)^*ᶠ[Λ].obj F)) :
    IsFieldLisseSheaf F := by
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  choose R' hR' hF using fun i ↦ h (f i) (.mk i)
  choose κ W g hg using fun i ↦ (R' i).exists_eq_ofArrows
  refine ⟨_, Precoverage.comp_mem_coverings f hR g (fun i ↦ hg i ▸ hR' i), ?_⟩
  rintro _ _ ⟨⟨i, j⟩⟩
  obtain ⟨n, ⟨e⟩⟩ := hF i (g i j) (by rw [hg i]; exact .mk j)
  exact ⟨n, ⟨(fieldUpperStarComp Λ _ _).app F ≪≫ e⟩⟩

/-- An extension of a sheaf isomorphic to `Λⁿ` by a lisse sheaf is lisse: the extension splits
locally. -/
theorem IsFieldLisseSheaf.of_shortExact_of_iso {S : ShortComplex (FieldSheaf Λ X)}
    (hS : S.ShortExact) (h₁ : IsFieldLisseSheaf S.X₁) (h₃ : IsFieldLisseSheaf S.X₃) {m : ℕ}
    (e : S.X₃ ≅ ⨁ fun _ : Fin m ↦ FieldSheaf.unit Λ X) :
    IsFieldLisseSheaf S.X₂ := by
  have := hS.epi_g
  obtain ⟨R, hR, h⟩ := exists_cover_field_lift (biproduct.map fun _ : Fin m ↦ S.g)
    (biproduct.lift fun k ↦ biproduct.ι (fun _ : Fin m ↦ FieldSheaf.unit Λ X) k ≫ e.inv)
  refine IsFieldLisseSheaf.of_presieve R hR fun W g hg ↦ ?_
  obtain ⟨hw, s, hs⟩ := h g hg
  let σ : (⨁ fun _ : Fin m ↦ FieldSheaf.unit Λ W) ⟶ (g)^*ᶠ[Λ].obj S.X₂ :=
    biproduct.desc fun k ↦ s ≫ (g)^*ᶠ[Λ].map (biproduct.π _ k)
  let τ : (⨁ fun _ : Fin m ↦ FieldSheaf.unit Λ W) ⟶ (g)^*ᶠ[Λ].obj S.X₃ :=
    biproduct.map (fun _ ↦ (fieldUpperStarUnitIso Λ g).inv) ≫
      ((g)^*ᶠ[Λ].mapBiproduct _).inv ≫ (g)^*ᶠ[Λ].map e.inv
  have hτ : σ ≫ (g)^*ᶠ[Λ].map S.g = τ := by
    refine biproduct.hom_ext' _ _ fun k ↦ ?_
    simp only [σ, τ, biproduct.ι_desc_assoc, Category.assoc, biproduct.ι_map_assoc,
      Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, ← Functor.map_comp]
    rw [show biproduct.π (fun _ ↦ S.X₂) k ≫ S.g =
        biproduct.map (fun _ : Fin m ↦ S.g) ≫ biproduct.π _ k by simp,
      Functor.map_comp, reassoc_of% hs, ← Functor.map_comp,
      biproduct.lift_π, Functor.map_comp]
  have hS' := hS.map_of_exact (g)^*ᶠ[Λ]
  have : IsIso (biproduct.map fun _ : Fin m ↦ (fieldUpperStarUnitIso Λ g).inv) :=
    (biproduct.mapIso fun _ ↦ (fieldUpperStarUnitIso Λ g).symm).isIso_hom
  have : IsIso τ := by dsimp only [τ]; infer_instance
  let sp := ShortComplex.Splitting.ofExactOfSection (S.map (g)^*ᶠ[Λ]) hS'.exact (inv τ ≫ σ)
    (by simp only [ShortComplex.map_g, Category.assoc, hτ, IsIso.inv_hom_id]) hS'.mono_f
  exact ((h₁.upperStar g).biprod (h₃.upperStar g)).of_iso sp.isoBinaryBiproduct.symm


/-- **Extensions of lisse sheaves are lisse**: on a cover trivialising the quotient, the extension
splits locally. -/
theorem IsFieldLisseSheaf.of_shortExact {S : ShortComplex (FieldSheaf Λ X)}
    (hS : S.ShortExact) (h₁ : IsFieldLisseSheaf S.X₁) (h₃ : IsFieldLisseSheaf S.X₃) :
    IsFieldLisseSheaf S.X₂ := by
  obtain ⟨R, hR, h⟩ := id h₃
  refine IsFieldLisseSheaf.of_presieve R hR fun V f hf ↦ ?_
  obtain ⟨m, ⟨e⟩⟩ := h f hf
  exact IsFieldLisseSheaf.of_shortExact_of_iso (S := S.map (f)^*ᶠ[Λ]) (hS.map_of_exact _)
    (h₁.upperStar f) (h₃.upperStar f) e

/-- **Extensions of stratified lisse sheaves are stratified lisse**: on the common refinement of
the two stratifications both ends are lisse. -/
theorem IsFieldStratifiedLisseSheaf.of_shortExact {S : ShortComplex (FieldSheaf Λ X)}
    (hS : S.ShortExact) (hF : IsFieldStratifiedLisseSheaf S.X₁)
    (hG : IsFieldStratifiedLisseSheaf S.X₃) : IsFieldStratifiedLisseSheaf S.X₂ := by
  obtain ⟨ι, hι, Z, i, hi, hc, hcover, h⟩ := hF
  obtain ⟨ι', hι', Z', i', hi', hc', hcover', h'⟩ := hG
  refine ⟨ι × ι', inferInstance, fun k ↦ pullback (i k.1) (i' k.2),
    fun k ↦ pullback.fst (i k.1) (i' k.2) ≫ i k.1, fun k ↦ inferInstance, fun k ↦ ?_,
    fun x ↦ ?_, fun k ↦ ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_fst,
      Set.image_preimage_eq_inter_range]
    exact (hc' k.2).inter (hc k.1)
  · obtain ⟨k, ⟨z, hz⟩, hk⟩ := hcover x
    obtain ⟨k', ⟨z', hz'⟩, hk'⟩ := hcover' x
    obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback z z' (hz.trans hz'.symm)
    refine ⟨(k, k'), ⟨t, by rw [Scheme.Hom.comp_apply, ht, hz]⟩, fun m ⟨t', ht'⟩ ↦ ?_⟩
    refine Prod.ext (hk m.1 ⟨_, ht'⟩) (hk' m.2 ⟨pullback.snd (i m.1) (i' m.2) t', ?_⟩)
    rw [← ht', ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  · let F := (pullback.fst (i k.1) (i' k.2) ≫ i k.1)^*ᶠ[Λ]
    have h₁ : IsFieldLisseSheaf (F.obj S.X₁) :=
      ((h k.1).upperStar (pullback.fst (i k.1) (i' k.2))).of_iso
        ((fieldUpperStarComp Λ (pullback.fst (i k.1) (i' k.2)) (i k.1)).app S.X₁).symm
    have h₃ : IsFieldLisseSheaf (F.obj S.X₃) :=
      (((h' k.2).upperStar (pullback.snd (i k.1) (i' k.2))).of_iso
        ((fieldUpperStarCompIso Λ pullback.condition.symm).app S.X₃)).of_iso
        ((fieldUpperStarComp Λ (pullback.fst (i k.1) (i' k.2)) (i k.1)).app S.X₃).symm
    exact IsFieldLisseSheaf.of_shortExact (S := S.map F) (hS.map_of_exact F) h₁ h₃

/-- **Extensions of constructible sheaves are constructible**: on the intersection of the two open
neighbourhoods both ends are stratified lisse. -/
theorem IsFieldConstructibleSheaf.of_shortExact {S : ShortComplex (FieldSheaf Λ X)}
    (hS : S.ShortExact) (hF : IsFieldConstructibleSheaf S.X₁)
    (hG : IsFieldConstructibleSheaf S.X₃) : IsFieldConstructibleSheaf S.X₂ := by
  intro x
  obtain ⟨W, j, hj, ⟨w, hw⟩, h⟩ := hF x
  obtain ⟨W', j', hj', ⟨w', hw'⟩, h'⟩ := hG x
  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback w w' (hw.trans hw'.symm)
  refine ⟨pullback j j', pullback.fst j j' ≫ j, inferInstance,
    ⟨t, by rw [Scheme.Hom.comp_apply, ht, hw]⟩, ?_⟩
  let F := (pullback.fst j j' ≫ j)^*ᶠ[Λ]
  have h₁ : IsFieldStratifiedLisseSheaf (F.obj S.X₁) :=
    (h.upperStar _).of_iso ((fieldUpperStarComp Λ (pullback.fst j j') j).app S.X₁).symm
  have h₃ : IsFieldStratifiedLisseSheaf (F.obj S.X₃) :=
    ((h'.upperStar (pullback.snd j j')).of_iso
      ((fieldUpperStarCompIso Λ pullback.condition.symm).app S.X₃)).of_iso
      ((fieldUpperStarComp Λ (pullback.fst j j') j).app S.X₃).symm
  exact IsFieldStratifiedLisseSheaf.of_shortExact (S := S.map F) (hS.map_of_exact F) h₁ h₃

end

instance {X : Scheme.{u}} : (fieldConstructibleSheaf Λ X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := IsFieldConstructibleSheaf.of_shortExact hS h₁ h₃

end AlgebraicGeometry.ProEtale
