/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.DenseOpenFunctions
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Lisse `ℓ`-adic sheaves extend uniquely over a dense open

Let `C` be a scheme with regular local rings, or more generally with local rings integrally
closed domains, and `j : U ⟶ C` a quasi-compact open immersion with dense image. For a lisse
`ℓ`-adic sheaf `F` on `C` the unit `F ⟶ j_* j^* F` of the adjunction `j^* ⊣ j_*` is an
isomorphism (see the main statements below).

For the constant sheaf `ℚ̄_ℓ` and a weakly étale `T ⟶ C`, the unit is the restriction of locally
finite functions from `T` to the preimage of `U`, which is bijective: `T` has integral local
rings (`AlgebraicGeometry.isDomain_stalk_of_weaklyEtale`,
`AlgebraicGeometry.isDomain_stalk_of_weaklyEtale_of_isIntegrallyClosed`), so locally finite
functions extend uniquely over the preimage of a dense open
(`AlgebraicGeometry.bijective_locallyFiniteFunctionsComp_of_isOpenImmersion`). The same holds
over every weakly étale `C`-scheme `V`, for the preimage of `U` in `V`. A lisse sheaf is, over
the members `V` of a pro-étale cover, a finite direct sum of copies of `ℚ̄_ℓ`, and the components
of the unit at `F` over weakly étale `C`-schemes factoring through `V` are components of the unit
over `V` at the restriction of `F`.

## Main statements

- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isIso_adicUpperStarLowerStarAdjunction_unit_app`:
  the regular case.
- `ProEtale.IsAdicLisseSheaf.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isIntegrallyClosed`:
  the normal case (blueprint `theorem-purity-real-sheaves-curves`, part (3)).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The component at a weakly étale `T ⟶ X` of the unit of the restriction adjunction
`ι^* ⊣ ι_*` along an open immersion `ι`: the restriction of sections along the projection
`T ×_X U ⟶ T`. -/
lemma openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app {A : Type*}
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {X V : Scheme.{u}}
    (ι : V ⟶ X) [IsOpenImmersion ι] (G : Sheaf (Scheme.ProEt.topology X) A) (T : X.ProEt) :
    ((openImmersionRestrictionLowerStarAdjunction A ι).unit.app G).hom.app (op T) =
      G.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ ι inferInstance
        trivial).counit.app T).op := by
  simp [openImmersionRestrictionLowerStarAdjunction, localizationRestrictionLowerStarAdjunction,
    Adjunction.sheafPushforwardContinuous]

/-- **The constant `ℓ`-adic sheaf is the direct image of its restriction to the preimage of a
dense open.** Let `p : X ⟶ C` be weakly étale, `C` such that schemes weakly étale over `C`
have integral local rings (e.g. `C` regular or normal), `j : U ⟶ C` a quasi-compact open
immersion with dense image and `ι : V ⟶ X` an open immersion onto `p⁻¹(j(U))`. Then the unit
`ℚ̄_ℓ,X ⟶ ι_* ι^* ℚ̄_ℓ,X` of the restriction adjunction is an isomorphism: over a weakly étale
`T ⟶ X` it is the restriction of locally finite functions from `T` to the preimage of `j(U)`. -/
theorem isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_adicConstantSheaf
    {X C U V : Scheme.{u}} (p : X ⟶ C) [WeaklyEtale p]
    (hC : ∀ ⦃W : Scheme.{u}⦄ (f : W ⟶ C) [WeaklyEtale f] (w : W),
      IsDomain (W.presheaf.stalk w))
    (j : U ⟶ C) [IsOpenImmersion j]
    [QuasiCompact j] (hj : Dense (Set.range j)) (ι : V ⟶ X) [IsOpenImmersion ι]
    (hι : Set.range ι = p ⁻¹' Set.range j) :
    IsIso ((openImmersionRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) ι).unit.app
      (adicConstantSheaf l X)) := by
  refine (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)).1 ?_
  suffices h : ∀ T : X.ProEt, IsIso (((openImmersionRestrictionLowerStarAdjunction
      (WeilCoefficients.{u} l) ι).unit.app (adicConstantSheaf l X)).hom.app (op T)) by
    have (T : X.ProEtᵒᵖ) : IsIso (((sheafToPresheaf _ _).map
        ((openImmersionRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) ι).unit.app
          (adicConstantSheaf l X))).app T) := h T.unop
    exact NatIso.isIso_of_isIso_app _
  intro T
  rw [openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app,
    ConcreteCategory.isIso_iff_bijective]
  have : WeaklyEtale T.hom := T.prop
  have hb := bijective_locallyFiniteFunctionsComp_of_isOpenImmersion (l := l) (T.hom ≫ p)
    (hC (T.hom ≫ p)) j hj (pullback.fst T.hom ι)
    (by
      rw [Scheme.Pullback.range_fst]
      ext x
      change T.hom x ∈ Set.range ι ↔ p (T.hom x) ∈ Set.range j
      rw [hι]
      rfl)
  refine ⟨fun a b h ↦ ULift.ext (hb.1 (congrArg ULift.down h)), fun b ↦ ?_⟩
  obtain ⟨a, ha⟩ := hb.2 b.down
  exact ⟨ULift.up a, congrArg ULift.up ha⟩

/-- **The unit at a finite free sheaf.** In the setting of the previous theorem, the unit
of the restriction adjunction is an isomorphism at every sheaf isomorphic to a finite direct sum
of copies of `ℚ̄_ℓ,X`. -/
theorem isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_of_iso_biproduct
    {X C U V : Scheme.{u}} (p : X ⟶ C) [WeaklyEtale p]
    (hC : ∀ ⦃W : Scheme.{u}⦄ (f : W ⟶ C) [WeaklyEtale f] (w : W),
      IsDomain (W.presheaf.stalk w))
    (j : U ⟶ C) [IsOpenImmersion j]
    [QuasiCompact j] (hj : Dense (Set.range j)) (ι : V ⟶ X) [IsOpenImmersion ι]
    (hι : Set.range ι = p ⁻¹' Set.range j) {H : Sheaf (Scheme.ProEt.topology X)
      (WeilCoefficients.{u} l)} {n : ℕ} (e : H ≅ ⨁ fun _ : Fin n ↦ adicConstantSheaf l X) :
    IsIso ((openImmersionRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) ι).unit.app
      H) := by
  have := NatTrans.isIso_app_biproduct
    (openImmersionRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) ι).unit
    (fun _ : Fin n ↦ adicConstantSheaf l X) fun _ ↦
      isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_adicConstantSheaf p hC j hj ι hι
  exact NatTrans.isIso_app_of_iso _ e

/-- **Sheaves locally free of finite rank extend uniquely over a dense open.** Let schemes
weakly étale over `C` have integral local rings, `j : U ⟶ C` be a quasi-compact open immersion
with dense image and `G` a sheaf on the pro-étale site of `C` whose restrictions to the members
`V i` of a pro-étale cover are finite direct sums of copies of `ℚ̄_ℓ`. Then the unit
`G ⟶ j_* j^* G` of the restriction adjunction is an isomorphism.

By conservativity of the restrictions to a cover it suffices to check this over each `V i`.
Over a weakly étale `T ⟶ V i`, the unit at `G` is the restriction of sections of `G` from `T` to
`T ×_C U`, which is, up to the identification `T ×_C U ≅ T ×_{V i} (V i ×_C U)`, the unit over
`V i` at the restriction of `G`, along the preimage `V i ×_C U ⟶ V i` of `U`. -/
theorem isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_of_cover
    {C U : Scheme.{u}}
    (hC : ∀ ⦃W : Scheme.{u}⦄ (f : W ⟶ C) [WeaklyEtale f] (w : W),
      IsDomain (W.presheaf.stalk w))
    (j : U ⟶ C)
    [IsOpenImmersion j] [QuasiCompact j] (hj : Dense (Set.range j))
    (G : Sheaf (Scheme.ProEt.topology C) (WeilCoefficients.{u} l)) {ι : Type*}
    {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ C) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows V g ∈ Scheme.proetalePrecoverage C)
    (hG : ∀ i, ∃ n : ℕ, Nonempty ((localizationRestriction (WeilCoefficients.{u} l) (g i)
      inferInstance).obj G ≅ ⨁ fun _ : Fin n ↦ adicConstantSheaf l (V i))) :
    IsIso ((openImmersionRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) j).unit.app
      G) := by
  refine isIso_of_isIso_localizationRestriction _ _ g hg fun i ↦ ?_
  obtain ⟨n, ⟨e⟩⟩ := hG i
  let ι' := pullback.fst (g i) j
  have hι' := isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_of_iso_biproduct
    (g i) hC j hj ι' (Scheme.Pullback.range_fst _ _) e
  refine (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)).1 ?_
  suffices h : ∀ T : (V i).ProEt, IsIso (((localizationRestriction (WeilCoefficients.{u} l) (g i)
      inferInstance).map ((openImmersionRestrictionLowerStarAdjunction (WeilCoefficients.{u} l)
        j).unit.app G)).hom.app (op T)) by
    have (T : (V i).ProEtᵒᵖ) : IsIso (((sheafToPresheaf _ _).map
        ((localizationRestriction (WeilCoefficients.{u} l) (g i) inferInstance).map
          ((openImmersionRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) j).unit.app
            G))).app T) := h T.unop
    exact NatIso.isIso_of_isIso_app _
  intro T
  rw [localizationRestriction_map_hom_app,
    openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app]
  -- the component over `V i` of the unit at the restriction of `G`
  have h₁ : IsIso (((openImmersionRestrictionLowerStarAdjunction (WeilCoefficients.{u} l)
      ι').unit.app ((localizationRestriction (WeilCoefficients.{u} l) (g i)
        inferInstance).obj G)).hom.app (op T)) :=
    have : IsIso ((sheafToPresheaf (Scheme.ProEt.topology (V i)) (WeilCoefficients.{u} l)).map
      ((openImmersionRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) ι').unit.app
        ((localizationRestriction (WeilCoefficients.{u} l) (g i) inferInstance).obj G))) :=
      inferInstance
    NatIso.isIso_app_of_isIso _ _
  rw [openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app] at h₁
  -- the identification `T ×_{V i} (V i ×_C U) ≅ T ×_C U`
  let θ : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale ι')).obj
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ ι').obj T)) ≅
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj
          ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))).obj T)) :=
    MorphismProperty.Over.isoMk (pullbackRightPullbackFstIso (g i) j T.hom) (by
      erw [pullbackRightPullbackFstIso_hom_snd_assoc, ← pullback.condition]
      simp [ι'])
  have hθ : θ.hom ≫ (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance
      trivial).counit.app ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))).obj
        T) = (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))).map
          ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ ι' inferInstance
            trivial).counit.app T) := by
    ext
    exact pullbackRightPullbackFstIso_hom_fst (g i) j T.hom
  have h₂ : G.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance
      trivial).counit.app ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))).obj
        T)).op = G.obj.map ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (g i))).map
          ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ ι' inferInstance
            trivial).counit.app T)).op ≫ G.obj.map θ.inv.op := by
    rw [← hθ, op_comp, G.obj.map_comp, Category.assoc, ← G.obj.map_comp, ← op_comp,
      θ.inv_hom_id, op_id, G.obj.map_id, Category.comp_id]
  rw [h₂]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ inferInstance

/-- The unit of `j^* ⊣ j_*` on sheaves along an open immersion is invertible exactly when the
unit of the restriction adjunction is: both left adjoints of `j_*` agree. -/
lemma isIso_upperStarLowerStarAdjunction_unit_app_iff {A : Type*} [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {X V : Scheme.{u}} (ι : V ⟶ X)
    [IsOpenImmersion ι] (G : Sheaf (Scheme.ProEt.topology X) A) :
    IsIso ((upperStarLowerStarAdjunction A ι).unit.app G) ↔
      IsIso ((openImmersionRestrictionLowerStarAdjunction A ι).unit.app G) := by
  let adj := upperStarLowerStarAdjunction A ι
  let adj' := openImmersionRestrictionLowerStarAdjunction A ι
  have h : adj.unit.app G =
      adj'.unit.app G ≫ (ι)_*[A].map ((adj.leftAdjointUniq adj').inv.app G) := by
    rw [← adj.unit_leftAdjointUniq_hom_app adj' G, Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  change IsIso (adj.unit.app G) ↔ IsIso (adj'.unit.app G)
  rw [h]
  exact ⟨fun _ ↦ IsIso.of_isIso_comp_right _ ((ι)_*[A].map ((adj.leftAdjointUniq adj').inv.app G)),
    fun _ ↦ inferInstance⟩

/-- **Lisse `ℓ`-adic sheaves extend uniquely over a dense open**, for a scheme `C` such that
every scheme weakly étale over `C` has integral local rings (e.g. `C` regular or normal). Let
`j : U ⟶ C` be a quasi-compact open immersion with dense image and `F` a lisse `ℓ`-adic sheaf
on `C`. Then the unit `F ⟶ j_* j^* F` of the adjunction `j^* ⊣ j_*` is an isomorphism. -/
theorem IsAdicLisseSheaf.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isDomain_stalk
    {C U : Scheme.{u}}
    (hC : ∀ ⦃W : Scheme.{u}⦄ (f : W ⟶ C) [WeaklyEtale f] (w : W),
      IsDomain (W.presheaf.stalk w))
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] (hj : Dense (Set.range j))
    {F : AdicSheaf l C} (hF : IsAdicLisseSheaf F) :
    IsIso ((adicUpperStarLowerStarAdjunction l j).unit.app F) := by
  obtain ⟨R, hR, hRF⟩ := hF
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  have hG (i : ι) : ∃ n : ℕ, Nonempty ((localizationRestriction (WeilCoefficients.{u} l) (f i)
      inferInstance).obj F.X ≅ ⨁ fun _ : Fin n ↦ adicConstantSheaf l (V i)) := by
    obtain ⟨n, ⟨e⟩⟩ := hRF (f i) (.mk i)
    exact ⟨n, ⟨((upperStarIsoLocalizationRestriction _ (f i) inferInstance).app F.X).symm ≪≫
      (AdicSheaf.forget (V i)).mapIso e ≪≫
        (AdicSheaf.forget (V i)).mapBiproduct fun _ : Fin n ↦ AdicSheaf.unit l (V i)⟩⟩
  have h := isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_of_cover hC j hj F.X f hR hG
  rw [← isIso_upperStarLowerStarAdjunction_unit_app_iff] at h
  have : IsIso ((Mod.forget _).map ((adicUpperStarLowerStarAdjunction l j).unit.app F)) := by
    change IsIso ((adicUpperStarLowerStarAdjunction l j).unit.app F).hom
    rw [adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_unit_app_hom]
    exact h
  exact isIso_of_reflects_iso _ (Mod.forget _)

/-- **Lisse `ℓ`-adic sheaves extend uniquely over a dense open of a normal scheme** (blueprint
`theorem-purity-real-sheaves-curves`, part (3), `ℓ`-adic level). Let `C` be a scheme whose local
rings are integrally closed domains, `j : U ⟶ C` a quasi-compact open immersion with dense image
and `F` a lisse `ℓ`-adic sheaf on `C`. Then the unit `F ⟶ j_* j^* F` of the adjunction
`j^* ⊣ j_*` is an isomorphism: schemes weakly étale over `C` have integral local rings
(`AlgebraicGeometry.isDomain_stalk_of_weaklyEtale_of_isIntegrallyClosed`). -/
theorem IsAdicLisseSheaf.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isIntegrallyClosed
    {C U : Scheme.{u}}
    (hC : ∀ c : C, IsDomain (C.presheaf.stalk c) ∧ IsIntegrallyClosed (C.presheaf.stalk c))
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] (hj : Dense (Set.range j))
    {F : AdicSheaf l C} (hF : IsAdicLisseSheaf F) :
    IsIso ((adicUpperStarLowerStarAdjunction l j).unit.app F) :=
  hF.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isDomain_stalk
    (fun _ f _ ↦ isDomain_stalk_of_weaklyEtale_of_isIntegrallyClosed f hC) j hj

/-- **Lisse `ℓ`-adic sheaves extend uniquely over a dense open.** Let `C` be a scheme with
regular local rings, `j : U ⟶ C` a quasi-compact open immersion with dense image and `F` a lisse
`ℓ`-adic sheaf on `C`. Then the unit `F ⟶ j_* j^* F` of the adjunction `j^* ⊣ j_*` is an
isomorphism. This is the `ℓ`-adic content of blueprint `lemma-boundary-stalk--2`; the
normal case is
`IsAdicLisseSheaf.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isIntegrallyClosed`. -/
theorem IsAdicLisseSheaf.isIso_adicUpperStarLowerStarAdjunction_unit_app {C U : Scheme.{u}}
    (hC : ∀ c : C, IsRegularLocalRing (C.presheaf.stalk c)) (j : U ⟶ C) [IsOpenImmersion j]
    [QuasiCompact j] (hj : Dense (Set.range j)) {F : AdicSheaf l C} (hF : IsAdicLisseSheaf F) :
    IsIso ((adicUpperStarLowerStarAdjunction l j).unit.app F) :=
  hF.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isDomain_stalk
    (fun _ f _ ↦ isDomain_stalk_of_weaklyEtale f hC) j hj

end AlgebraicGeometry.ProEtale
