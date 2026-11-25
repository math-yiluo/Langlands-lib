/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalization
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafIso
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralCoefficientLimit
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

/-!
# The rationalization formula for `ℤ_ℓ,X`

The rationalization comparison
`κ : ⨁_{b ∈ B} colim (M --ℓ--> M --ℓ--> ⋯) ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} M`
(`AlgebraicGeometry.ProEtale.rationalizationComparison`) is an isomorphism for `M = ℤ_ℓ,X`
(`AlgebraicGeometry.ProEtale.isIso_rationalizationComparison_app_regular`). Identifying
`ℚ̄_ℓ ⊗ ℤ_ℓ,X ≅ ℚ̄_ℓ,X` (`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsRegularIso`), under
which the unit is the inclusion `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X`
(`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsUnitAb_regular_comp`), the comparison sends
`g` in the `n`-th copy of the summand `b` to `b ℓ⁻ⁿ g`, and it is the composite of

* `colim (ℤ_ℓ,X --ℓ--> ℤ_ℓ,X --ℓ--> ⋯) ≅ ℚ_ℓ,X`, `g ↦ ℓ⁻ⁿ g`
  (`AlgebraicGeometry.ProEtale.isColimitPadicAbSheafCocone`): on sections the presheaf colimit
  is the group of the functions `ℓ⁻ⁿ g`, which are locally all continuous functions to `ℚ_ℓ`,
  a continuous function on an affine (hence compact) open being bounded
  (`PadicAlgCl.exists_padicInt_eq_pow_mul`);
* `⨁_{b ∈ B} ℚ_ℓ,X ≅ ℚ̄_ℓ,X`, `(q_b) ↦ ∑ b q_b`
  (`AlgebraicGeometry.ProEtale.isColimitAdicAbSheafCocone`): on sections the map from the
  presheaf direct sum is injective, `B` being linearly independent, and locally surjective, a
  locally finite function being near every point a finite combination of elements of `B` with
  continuous coefficients (`AlgebraicGeometry.ProEtale.exists_finset_sum_padicAlgClBasisIndex`).

Both are instances of `CategoryTheory.Sheaf.isColimitOfW`: a cocone of sheaves is a colimit
cocone if it receives a locally bijective map from a colimit cocone of the underlying presheaves.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped Obj

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
  [HasWeakSheafify J A] {K : Type*} [Category* K]

/-- A cocone `c` of sheaves is a colimit cocone if there is a colimit cocone `E` of the
underlying presheaves and a morphism `E.pt ⟶ c.pt` of presheaves compatible with the cocone
maps which becomes an isomorphism after sheafification. -/
noncomputable def isColimitOfW {F : K ⥤ Sheaf J A} (c : Cocone F)
    (E : Cocone (F ⋙ sheafToPresheaf J A)) (hE : IsColimit E) (ψ : E.pt ⟶ c.pt.obj)
    (hψ : ∀ k, E.ι.app k ≫ ψ = (c.ι.app k).hom) (hW : J.W ψ) : IsColimit c :=
  have : IsIso (((sheafificationAdjunction J A).homEquiv _ c.pt).symm ψ) := by
    rw [GrothendieckTopology.W_iff] at hW
    rw [Adjunction.homEquiv_counit]
    infer_instance
  IsColimit.ofIsoColimit (isColimitSheafifyCocone E hE)
    (Cocone.ext (asIso (((sheafificationAdjunction J A).homEquiv _ c.pt).symm ψ)) fun k ↦ by
      refine ObjectProperty.hom_ext _ ?_
      rw [ObjectProperty.FullSubcategory.comp_hom, sheafifyCocone_ι_app_val_assoc, asIso_hom]
      erw [toSheafify_sheafifyLift J ψ c.pt.property]
      exact hψ k)

end CategoryTheory.Sheaf

namespace AddCommGrpCat

universe v

/-- A cocone over a filtered diagram of abelian groups whose maps are injective and jointly
surjective is a colimit cocone. -/
noncomputable def isColimitOfInjective {J : Type} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ AddCommGrpCat.{v}} (c : Cocone F)
    (hsurj : ∀ x : c.pt, ∃ i xi, x = c.ι.app i xi)
    (hinj : ∀ i, Function.Injective (c.ι.app i)) : IsColimit c :=
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (forget AddCommGrpCat.{v})
  have := reflectsColimitsOfShape_of_reflectsIsomorphisms (G := forget AddCommGrpCat.{v}) (J := J)
  isColimitOfReflects (forget _) (Types.FilteredColimit.isColimitOf' _ _
    (fun x ↦ by
      obtain ⟨i, xi, h⟩ := hsurj x
      exact ⟨i, xi, h⟩)
    fun i x y h ↦ ⟨i, 𝟙 i, by
      rw [CategoryTheory.Functor.map_id]
      exact hinj i h⟩)

section DirectSum

variable {B : Type} [DecidableEq B] (G : Discrete B ⥤ AddCommGrpCat.{v})

/-- The cocone over a discrete diagram of abelian groups with point the direct sum. -/
noncomputable def directSumCocone : Cocone G :=
  Cocone.mk (of (DirectSum B fun b ↦ G.obj ⟨b⟩))
    (Discrete.natTrans fun b ↦ ofHom (DirectSum.of (fun b ↦ G.obj ⟨b⟩) b.as))

/-- The direct sum is the coproduct of abelian groups. -/
noncomputable def isColimitDirectSumCocone : IsColimit (directSumCocone G) where
  desc s := ofHom (DirectSum.toAddMonoid fun b ↦ (s.ι.app ⟨b⟩).hom)
  fac s := by
    rintro ⟨b⟩
    ext x
    simp [directSumCocone]
  uniq s m hm := AddCommGrpCat.hom_ext (DirectSum.addHom_ext fun b x ↦ by
    rw [hom_ofHom, DirectSum.toAddMonoid_of, ← hm ⟨b⟩]
    rfl)

end DirectSum

end AddCommGrpCat

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- **The unit of `ℤ_ℓ,X` is the inclusion `ℤ_ℓ,X ⟶ ℚ̄_ℓ,X`**: the unit `ℤ_ℓ,X ⟶ ℚ̄_ℓ ⊗ ℤ_ℓ,X`
followed by `ℚ̄_ℓ ⊗ ℤ_ℓ,X ≅ ℚ̄_ℓ,X` is the inclusion. -/
lemma adicSheafExtendScalarsUnitAb_regular_comp :
    adicSheafExtendScalarsUnitAb l X (Mod.regular (padicIntAbSheaf X l)) ≫
      (AdicSheaf.toAb l X).map (adicSheafExtendScalarsRegularIso l X).hom =
      padicIntSheafToAdicConstantSheaf X l := by
  have h : (Mod.extendHomEquiv (freePadicIntSheafToAdicConstantSheaf X l)
      (((weilCoefficientsFree X l).mapMod (padicIntAbSheaf X l)).obj
        (Mod.regular (padicIntAbSheaf X l))) (AdicSheaf.unit l X)
      (Mod.extendScalarsMap (freePadicIntSheafToAdicConstantSheaf X l)
        ((weilCoefficientsFree X l).mapModRegularIso (padicIntAbSheaf X l)).hom ≫
        Mod.extendHom (freePadicIntSheafToAdicConstantSheaf X l)
          (Mod.regularHomComap (freePadicIntSheafToAdicConstantSheaf X l)))).hom =
      freePadicIntSheafToAdicConstantSheaf X l := by
    rw [Mod.extendHomEquiv_apply, Mod.comp_hom', Mod.comap_map_hom, Mod.extendUnit_hom,
      Mod.comp_hom', Mod.extendUnitHom_extendScalarsMap_assoc, Mod.extendUnitHom_extendHom]
    erw [Category.id_comp]
    rfl
  have key : ((adicSheafExtendScalarsRestrictAdjunction X l).homEquiv _ _
      (adicSheafExtendScalarsRegularIso l X).hom).hom = padicIntSheafToAdicConstantSheaf X l := by
    rw [adicSheafExtendScalarsRestrictAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv]
    dsimp [Mod.extendRestrictAdjunction, Adjunction.mkOfHomEquiv, Mod.extendHomEquiv,
      Adjunction.mapModAdjunction, adicSheafExtendScalarsRegularIso,
      Mod.extendScalarsObjRegularIso, comapMapModComapIsoRestrictPadicInt]
    simp only [Adjunction.mk'_homEquiv]
    simp only [Mod.extendScalars_map, Equiv.coe_fn_mk, Mod.Hom.mk'_hom, Mod.id_hom',
      Mod.comap_map_hom, Functor.mapModComapIso_hom_app_hom, Mod.comapComp_inv_app_hom,
      Category.id_comp]
    erw [h, Equiv.apply_symm_apply, Category.comp_id]
  exact (congrArg Mod.Hom.hom ((adicSheafExtendScalarsRestrictAdjunction X l).homEquiv_unit _ _
    (adicSheafExtendScalarsRegularIso l X).hom)).symm.trans key

/-! ### `ℚ_ℓ,X = colim (ℤ_ℓ,X --ℓ--> ℤ_ℓ,X --ℓ--> ⋯)` -/

section PadicSheaf

variable {l} in
/-- The map `g ↦ ℓ⁻ⁿ g` from the continuous functions to `ℤ_ℓ` to those to `ℚ_ℓ`. -/
noncomputable def padicIntScaled (T : Type*) [TopologicalSpace T] (n : ℕ) :
    C(T, ℤ_[l]) →+ C(T, ℚ_[l]) where
  toFun g := ((l : ℚ_[l]) ^ n)⁻¹ •
    (⟨((↑) : ℤ_[l] → ℚ_[l]), continuous_subtype_val⟩ : C(ℤ_[l], ℚ_[l])).comp g
  map_zero' := by
    ext
    simp
  map_add' _ _ := by
    ext
    simp [mul_add]

/-- The values of `g ↦ ℓ⁻ⁿ g`. -/
lemma padicIntScaled_apply {T : Type*} [TopologicalSpace T] (n : ℕ) (g : C(T, ℤ_[l])) (t : T) :
    padicIntScaled (l := l) T n g t = ((l : ℚ_[l]) ^ n)⁻¹ * (g t : ℚ_[l]) :=
  rfl

/-- `g ↦ ℓ⁻ⁿ g` is injective. -/
lemma padicIntScaled_injective {T : Type*} [TopologicalSpace T] (n : ℕ) :
    Function.Injective (padicIntScaled (l := l) T n) := by
  intro g h hgh
  ext t
  have hl : ((l : ℚ_[l]) ^ n)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have := congrArg (fun f : C(T, ℚ_[l]) ↦ f t) hgh
  simp only [padicIntScaled_apply] at this
  exact mul_left_cancel₀ hl this

variable {l} in
/-- The continuous functions `T → ℚ_ℓ` of the form `ℓ⁻ⁿ g` for a continuous `g : T → ℤ_ℓ`. -/
noncomputable def scaledPadicIntFunctions (T : Type*) [TopologicalSpace T] :
    AddSubgroup C(T, ℚ_[l]) where
  carrier := {f | ∃ n g, padicIntScaled T n g = f}
  zero_mem' := ⟨0, 0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨n, g, rfl⟩ ⟨m, h, rfl⟩
    refine ⟨n + m, (l : ℤ_[l]) ^ m • g + (l : ℤ_[l]) ^ n • h, ?_⟩
    have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    ext t
    simp only [padicIntScaled_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      smul_eq_mul, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
    field_simp
    ring
  neg_mem' := by
    rintro _ ⟨n, g, rfl⟩
    exact ⟨n, -g, map_neg _ _⟩

/-- The abelian sheaf underlying `ℚ_ℓ,X`. -/
noncomputable abbrev padicAbSheaf : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicSheaf X l)

/-- The map `g ↦ ℓ⁻ⁿ g` from `ℤ_ℓ,X` to `ℚ_ℓ,X`. -/
noncomputable def padicIntScaledHom (n : ℕ) : padicIntAbSheaf X l ⟶ padicAbSheaf l X :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun x := ULift.up (padicIntScaled U.unop.left n x.down)
          map_zero' := congrArg ULift.up (map_zero _)
          map_add' x y := congrArg ULift.up (map_add _ x.down y.down) }
      naturality _ _ _ := rfl }

/-- The sections of `g ↦ ℓ⁻ⁿ g`. -/
@[simp]
lemma padicIntScaledHom_hom_app_apply_down (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : (padicIntAbSheaf X l).obj.obj U) :
    ((padicIntScaledHom l X n).hom.app U x).down = padicIntScaled U.unop.left n x.down :=
  rfl

/-- `ℓ⁻⁽ⁿ⁺¹⁾ (ℓ g) = ℓ⁻ⁿ g`. -/
lemma zsmul_id_comp_padicIntScaledHom (n : ℕ) :
    ((l : ℤ) • 𝟙 (padicIntAbSheaf X l)) ≫ padicIntScaledHom l X (n + 1) =
      padicIntScaledHom l X n := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  rw [Preadditive.zsmul_comp, Category.id_comp]
  ext U x
  refine ULift.ext (ContinuousMap.ext fun t ↦ ?_)
  have h : ((l : ℤ) • (padicIntScaledHom l X (n + 1)).hom.app U x).down t =
      (l : ℤ) • ((padicIntScaledHom l X (n + 1)).hom.app U x).down t := rfl
  erw [h]
  rw [padicIntScaledHom_hom_app_apply_down, padicIntScaledHom_hom_app_apply_down,
    padicIntScaled_apply, padicIntScaled_apply, zsmul_eq_mul, Int.cast_natCast, pow_succ]
  field_simp

/-- The cocone `(g ↦ ℓ⁻ⁿ g)ₙ` over `ℤ_ℓ,X --ℓ--> ℤ_ℓ,X --ℓ--> ⋯` with point `ℚ_ℓ,X`. -/
noncomputable def padicAbSheafCocone : Cocone ((ellMulTower l).obj (padicIntAbSheaf X l)) :=
  Cocone.mk (padicAbSheaf l X)
    (NatTrans.ofSequence (fun n ↦ padicIntScaledHom l X n) fun n ↦ by
      rw [ellMulTower_obj_map_succ, zsmul_id_comp_padicIntScaledHom]
      exact (Category.comp_id _).symm)

/-- The presheaf of the continuous functions `U → ℚ_ℓ` of the form `ℓ⁻ⁿ g` with `g : U → ℤ_ℓ`
continuous, whose sheafification is `ℚ_ℓ,X`. -/
noncomputable def scaledPadicIntPresheaf : X.ProEtᵒᵖ ⥤ Ab.{u + 1} where
  obj U := AddCommGrpCat.of (ULift.{u + 1} (scaledPadicIntFunctions (l := l) U.unop.left))
  map f := AddCommGrpCat.ofHom
    { toFun x := ULift.up ⟨x.down.1.comp f.unop.left.base.hom, by
        obtain ⟨n, g, hg⟩ := x.down.2
        exact ⟨n, g.comp f.unop.left.base.hom, by rw [← hg]; rfl⟩⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The map `g ↦ ℓ⁻ⁿ g` from `ℤ_ℓ,X` to the presheaf `scaledPadicIntPresheaf`. -/
noncomputable def padicIntToScaledPadicIntPresheaf (n : ℕ) :
    (padicIntAbSheaf X l).obj ⟶ scaledPadicIntPresheaf l X where
  app _ := AddCommGrpCat.ofHom
    { toFun x := ULift.up ⟨padicIntScaled _ n x.down, n, x.down, rfl⟩
      map_zero' := ULift.ext (Subtype.ext (map_zero _))
      map_add' x y := ULift.ext (Subtype.ext (map_add _ x.down y.down)) }
  naturality _ _ _ := rfl

/-- The inclusion of `scaledPadicIntPresheaf` into `ℚ_ℓ,X`. -/
noncomputable def scaledPadicIntPresheafToPadicAbSheaf :
    scaledPadicIntPresheaf l X ⟶ (padicAbSheaf l X).obj where
  app _ := AddCommGrpCat.ofHom
    { toFun x := ULift.up x.down.1
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

/-- The map `g ↦ ℓ⁻ⁿ g` to `scaledPadicIntPresheaf` lifts `g ↦ ℓ⁻ⁿ g` to `ℚ_ℓ,X`. -/
lemma padicIntToScaledPadicIntPresheaf_comp (n : ℕ) :
    padicIntToScaledPadicIntPresheaf l X n ≫ scaledPadicIntPresheafToPadicAbSheaf l X =
      (padicIntScaledHom l X n).hom :=
  rfl

/-- The inclusion of `scaledPadicIntPresheaf` into `ℚ_ℓ,X` is injective. -/
lemma injective_scaledPadicIntPresheafToPadicAbSheaf_app (U : X.ProEtᵒᵖ) :
    Function.Injective ((scaledPadicIntPresheafToPadicAbSheaf l X).app U) := fun _ _ h ↦
  ULift.ext (Subtype.ext (congrArg ULift.down h))

/-- The inclusion of `scaledPadicIntPresheaf` into `ℚ_ℓ,X` is a monomorphism. -/
instance : Mono (scaledPadicIntPresheafToPadicAbSheaf l X) := by
  have (U : X.ProEtᵒᵖ) : Mono ((scaledPadicIntPresheafToPadicAbSheaf l X).app U) :=
    (AddCommGrpCat.mono_iff_injective _).2
      (injective_scaledPadicIntPresheafToPadicAbSheaf_app l X U)
  exact NatTrans.mono_of_mono_app _

/-- The cocone `(g ↦ ℓ⁻ⁿ g)ₙ` of presheaves over `ℤ_ℓ,X --ℓ--> ℤ_ℓ,X --ℓ--> ⋯` with point
`scaledPadicIntPresheaf`. -/
noncomputable def scaledPadicIntPresheafCocone :
    Cocone ((ellMulTower l).obj (padicIntAbSheaf X l) ⋙ sheafToPresheaf _ _) :=
  Cocone.mk (scaledPadicIntPresheaf l X)
    (NatTrans.ofSequence (fun n ↦ padicIntToScaledPadicIntPresheaf l X n) fun n ↦ by
      rw [← cancel_mono (scaledPadicIntPresheafToPadicAbSheaf l X), Category.assoc,
        padicIntToScaledPadicIntPresheaf_comp]
      erw [Category.comp_id]
      rw [padicIntToScaledPadicIntPresheaf_comp]
      exact congrArg (fun φ ↦ φ.hom) ((padicAbSheafCocone l X).w (homOfLE (Nat.le_succ n))))

/-- The cocone `scaledPadicIntPresheafCocone` is a colimit cocone: sectionwise, every function
`ℓ⁻ⁿ g` comes from the `n`-th copy, and the maps `g ↦ ℓ⁻ⁿ g` are injective. -/
noncomputable def isColimitScaledPadicIntPresheafCocone :
    IsColimit (scaledPadicIntPresheafCocone l X) :=
  evaluationJointlyReflectsColimits _ fun _ ↦
    AddCommGrpCat.isColimitOfInjective _
      (fun x ↦ ⟨x.down.2.choose, ULift.up x.down.2.choose_spec.choose,
        ULift.ext (Subtype.ext x.down.2.choose_spec.choose_spec.symm)⟩)
      fun n _ _ h ↦ ULift.ext (padicIntScaled_injective l n
        (congrArg (fun z ↦ z.down.1) h))

/-- The inclusion of `scaledPadicIntPresheaf` into `ℚ_ℓ,X` is locally injective. -/
instance isLocallyInjective_scaledPadicIntPresheafToPadicAbSheaf :
    Presheaf.IsLocallyInjective (ProEt.topology X) (scaledPadicIntPresheafToPadicAbSheaf l X) :=
  Presheaf.isLocallyInjective_of_injective _ _
    (injective_scaledPadicIntPresheafToPadicAbSheaf_app l X)

/-- A continuous function to `ℚ_ℓ` is, on the affine opens, `ℓ⁻ⁿ` times an integral one, and
open covers are coverings of `X_proét`. -/
instance isLocallySurjective_scaledPadicIntPresheafToPadicAbSheaf :
    Presheaf.IsLocallySurjective (ProEt.topology X) (scaledPadicIntPresheafToPadicAbSheaf l X) where
  imageSieve_mem {U} s := by
    choose W hW hxW _ using fun x : U.left ↦
      exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
    refine (ProEt.topology X).superset_covering ?_ (ProEt.generate_ofArrows_mem_topology U
      W fun x ↦ ⟨x, hxW x⟩)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨x⟩
    have : IsAffine (W x).toScheme := hW x
    have : CompactSpace (ProEt.ofOpens U (W x)).left :=
      (inferInstance : CompactSpace (W x).toScheme)
    obtain ⟨m, g, hg⟩ := PadicAlgCl.exists_padicInt_eq_pow_mul
      (s.down.comp (W x).ι.base.hom : C((ProEt.ofOpens U (W x)).left, ℚ_[l]))
    refine ⟨ULift.up ⟨s.down.comp (W x).ι.base.hom, m, g, ?_⟩, rfl⟩
    have hl : (l : ℚ_[l]) ^ m ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    ext t
    rw [padicIntScaled_apply, hg t, inv_mul_cancel_left₀ hl]

/-- **`ℚ_ℓ,X = colim (ℤ_ℓ,X --ℓ--> ℤ_ℓ,X --ℓ--> ⋯)`**: the cocone `(g ↦ ℓ⁻ⁿ g)ₙ` is a colimit
cocone of abelian sheaves. -/
noncomputable def isColimitPadicAbSheafCocone : IsColimit (padicAbSheafCocone l X) :=
  Sheaf.isColimitOfW _ _ (isColimitScaledPadicIntPresheafCocone l X)
    (scaledPadicIntPresheafToPadicAbSheaf l X) (fun _ ↦ rfl)
    ((GrothendieckTopology.W_iff_isLocallyBijective _ _).2 ⟨inferInstance, inferInstance⟩)

end PadicSheaf

/-! ### `ℚ̄_ℓ,X = ⨁_{b ∈ B} ℚ_ℓ,X` -/

section PadicAlgClSheaf

variable {l} in
/-- The inclusion of the continuous functions to `ℚ_ℓ` into the locally finite functions to
`ℚ̄_ℓ`. -/
noncomputable def padicToLocallyFiniteFunctions (T : Type*) [TopologicalSpace T] :
    C(T, ℚ_[l]) →+ PadicAlgCl.locallyFiniteFunctions l T where
  toFun q := ⟨(⟨algebraMap ℚ_[l] (PadicAlgCl l), continuous_algebraMap _ _⟩ :
      C(ℚ_[l], PadicAlgCl l)).comp q, fun x ↦ ⟨Set.univ, Filter.univ_mem,
    Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ_[l] {1}) (Submodule.span_le.2 (by
      rintro _ ⟨y, -, rfl⟩
      exact Submodule.mem_span_singleton.2 ⟨q y, by simp [Algebra.smul_def]⟩))⟩⟩
  map_zero' := Subtype.ext (ContinuousMap.ext fun _ ↦ by simp)
  map_add' _ _ := Subtype.ext (ContinuousMap.ext fun _ ↦ by simp)

/-- The values of the inclusion `C(T, ℚ_ℓ) → ℚ̄_ℓ,T`. -/
lemma padicToLocallyFiniteFunctions_apply {T : Type*} [TopologicalSpace T] (q : C(T, ℚ_[l]))
    (t : T) :
    (padicToLocallyFiniteFunctions T q : C(T, PadicAlgCl l)) t =
      algebraMap ℚ_[l] (PadicAlgCl l) (q t) :=
  rfl

/-- The abelian sheaf underlying `ℚ̄_ℓ,X`. -/
noncomputable abbrev adicAbSheaf : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)

/-- The map `q ↦ b q` from `ℚ_ℓ,X` to `ℚ̄_ℓ,X`, for `b ∈ ℚ̄_ℓ`. -/
noncomputable def padicAbSheafMulHom (b : PadicAlgCl l) : padicAbSheaf l X ⟶ adicAbSheaf l X :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun x := ULift.up ((DistribSMul.toAddMonoidHom _ b).comp
            (padicToLocallyFiniteFunctions (l := l) U.unop.left) x.down)
          map_zero' := congrArg ULift.up (map_zero _)
          map_add' x y := congrArg ULift.up (map_add _ x.down y.down) }
      naturality _ _ _ := rfl }

/-- The sections of `q ↦ b q`. -/
@[simp]
lemma padicAbSheafMulHom_hom_app_apply_down (b : PadicAlgCl l) (U : X.ProEtᵒᵖ)
    (x : (padicAbSheaf l X).obj.obj U) :
    ((padicAbSheafMulHom l X b).hom.app U x).down =
      b • padicToLocallyFiniteFunctions U.unop.left x.down :=
  rfl

/-- The cocone `(q ↦ b q)_{b ∈ B}` over `⨁_{b ∈ B} ℚ_ℓ,X` with point `ℚ̄_ℓ,X`. -/
noncomputable def adicAbSheafCocone :
    Cocone ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj (padicAbSheaf l X)) :=
  Cocone.mk (adicAbSheaf l X) (Discrete.natTrans fun b ↦ padicAbSheafMulHom l X b.as)

/-- A choice of decidable equality on the basis `B` of `ℚ̄_ℓ` over `ℚ_ℓ`. -/
@[instance_reducible]
noncomputable def padicAlgClBasisIndexDecidableEq : DecidableEq (padicAlgClBasisIndex l) :=
  Classical.decEq _

attribute [local instance] padicAlgClBasisIndexDecidableEq

/-- The presheaf `U ↦ ⨁_{b ∈ B} C(U, ℚ_ℓ)`. -/
noncomputable def padicDirectSumPresheaf : X.ProEtᵒᵖ ⥤ Ab.{u + 1} where
  obj U := AddCommGrpCat.of (DirectSum (padicAlgClBasisIndex l)
    fun _ ↦ (padicAbSheaf l X).obj.obj U)
  map f := AddCommGrpCat.ofHom (DirectSum.map fun _ ↦ ((padicAbSheaf l X).obj.map f).hom)
  map_id U := by
    ext x b
    simp
  map_comp f g := by
    ext x b
    simp

/-- The cocone of presheaves over `⨁_{b ∈ B} ℚ_ℓ,X` with point `U ↦ ⨁_{b ∈ B} C(U, ℚ_ℓ)`. -/
noncomputable def padicDirectSumPresheafCocone :
    Cocone ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj (padicAbSheaf l X) ⋙
      sheafToPresheaf _ _) :=
  Cocone.mk (padicDirectSumPresheaf l X) (Discrete.natTrans fun b ↦
    { app U := AddCommGrpCat.ofHom (DirectSum.of (fun _ ↦ (padicAbSheaf l X).obj.obj U) b.as)
      naturality U V f := by
        ext x
        exact (DirectSum.map_of (fun _ ↦ ((padicAbSheaf l X).obj.map f).hom) b.as x).symm })

/-- The cocone `padicDirectSumPresheafCocone` is a colimit cocone, being sectionwise the direct
sum. -/
noncomputable def isColimitPadicDirectSumPresheafCocone :
    IsColimit (padicDirectSumPresheafCocone l X) :=
  evaluationJointlyReflectsColimits _ fun _ ↦
    IsColimit.ofIsoColimit (AddCommGrpCat.isColimitDirectSumCocone _)
      (Cocone.ext (Iso.refl _) fun _ ↦ Category.comp_id _)

/-- The map `⨁_{b ∈ B} C(U, ℚ_ℓ) ⟶ ℚ̄_ℓ,X(U)`, `(q_b) ↦ ∑ b q_b`. -/
noncomputable def padicDirectSumPresheafToAdicAbSheaf :
    padicDirectSumPresheaf l X ⟶ (adicAbSheaf l X).obj where
  app U := AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun b ↦
    ((padicAbSheafMulHom l X (b : PadicAlgCl l)).hom.app U).hom)
  naturality U V f := by
    ext : 1
    refine DirectSum.addHom_ext fun b x ↦ ?_
    simp only [padicDirectSumPresheaf, AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom,
      AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.map_of]
    erw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    exact ConcreteCategory.congr_hom ((padicAbSheafMulHom l X b).hom.naturality f) x

/-- The basis `B` of `ℚ̄_ℓ` over `ℚ_ℓ` is linearly independent. -/
lemma linearIndependent_padicAlgClBasisIndex :
    LinearIndependent ℚ_[l] (fun b : padicAlgClBasisIndex l ↦ (b : PadicAlgCl l)) := by
  simpa using (Module.Basis.ofVectorSpace ℚ_[l] (PadicAlgCl l)).linearIndependent

/-- A continuous function `f : T → ℚ̄_ℓ` whose values span a finite-dimensional `ℚ_ℓ`-subspace
is a finite combination `∑_{b ∈ S} q_b b` of elements of the basis `B` of `ℚ̄_ℓ` over `ℚ_ℓ`, with
continuous coefficients `q_b : T → ℚ_ℓ`: the coordinates are continuous on the
finite-dimensional span of the values. -/
lemma exists_finset_sum_padicAlgClBasisIndex {T : Type*} [TopologicalSpace T]
    (f : C(T, PadicAlgCl l))
    (hf : FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (Set.range f))) :
    ∃ (S : Finset (padicAlgClBasisIndex l)) (q : padicAlgClBasisIndex l → C(T, ℚ_[l])),
      ∀ t, f t = ∑ b ∈ S, q b t • (b : PadicAlgCl l) := by
  classical
  let V := Submodule.span ℚ_[l] (Set.range f)
  let Bs := Module.Basis.ofVectorSpace ℚ_[l] (PadicAlgCl l)
  let e := Module.finBasis ℚ_[l] V
  let L (b : padicAlgClBasisIndex l) : V →ₗ[ℚ_[l]] ℚ_[l] :=
    Finsupp.lapply b ∘ₗ Bs.repr.toLinearMap ∘ₗ V.subtype
  let g : C(T, V) := ⟨fun t ↦ ⟨f t, Submodule.subset_span ⟨t, rfl⟩⟩,
    f.continuous.subtype_mk _⟩
  let S : Finset (padicAlgClBasisIndex l) :=
    Finset.univ.biUnion fun i ↦ (Bs.repr (e i)).support
  have hL (b : padicAlgClBasisIndex l) (hb : b ∉ S) : L b = 0 :=
    e.ext fun i ↦ Finsupp.notMem_support_iff.1 fun h ↦
      hb (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, h⟩)
  refine ⟨S, fun b ↦ ⟨fun t ↦ L b (g t), (L b).continuous_of_finiteDimensional.comp
    g.continuous⟩, fun t ↦ ?_⟩
  have hsupp : (Bs.repr (f t)).support ⊆ S := fun b hb ↦ by
    by_contra hbS
    exact Finsupp.mem_support_iff.1 hb (LinearMap.congr_fun (hL b hbS) (g t))
  conv_lhs => rw [← Bs.linearCombination_repr (f t), Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset _ hsupp (fun b a ↦ a • Bs b) fun _ _ ↦ zero_smul _ _]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Module.Basis.coe_ofVectorSpace]
  rfl

/-- `(q_b) ↦ ∑ b q_b` is injective, `B` being linearly independent over `ℚ_ℓ`. -/
lemma injective_padicDirectSumPresheafToAdicAbSheaf_app (U : X.ProEtᵒᵖ) :
    Function.Injective ((padicDirectSumPresheafToAdicAbSheaf l X).app U) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro (x : DirectSum (padicAlgClBasisIndex l) fun _ ↦ (padicAbSheaf l X).obj.obj U) hx
  have key (t : U.unop.left) : ∀ b ∈ x.support, (x b).down t = 0 := by
    refine linearIndependent_iff'.1 (linearIndependent_padicAlgClBasisIndex l) x.support
      (fun b ↦ (x b).down t) ?_
    let ev : (adicAbSheaf l X).obj.obj U →+ PadicAlgCl l :=
      { toFun y := y.down.1 t
        map_zero' := rfl
        map_add' _ _ := rfl }
    have h := congrArg ev hx
    rw [map_zero] at h
    rw [← h]
    simp only [padicDirectSumPresheafToAdicAbSheaf, AddCommGrpCat.hom_ofHom,
      DirectSum.toAddMonoid, DFinsupp.liftAddHom_apply]
    erw [DFinsupp.sumAddHom_apply]
    rw [DFinsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
    rfl
  refine DirectSum.ext fun b ↦ ?_
  by_cases hb : b ∈ x.support
  · exact ULift.ext (ContinuousMap.ext fun t ↦ key t b hb)
  · simpa using hb

/-- `(q_b) ↦ ∑ b q_b` is locally injective. -/
instance isLocallyInjective_padicDirectSumPresheafToAdicAbSheaf :
    Presheaf.IsLocallyInjective (ProEt.topology X) (padicDirectSumPresheafToAdicAbSheaf l X) :=
  Presheaf.isLocallyInjective_of_injective _ _
    (injective_padicDirectSumPresheafToAdicAbSheaf_app l X)

/-- A locally finite function is, near every point, a finite combination `∑_{b ∈ S} q_b b` with
continuous coefficients `q_b` to `ℚ_ℓ`, and open covers are coverings of `X_proét`. -/
instance isLocallySurjective_padicDirectSumPresheafToAdicAbSheaf :
    Presheaf.IsLocallySurjective (ProEt.topology X) (padicDirectSumPresheafToAdicAbSheaf l X) where
  imageSieve_mem {U} s := by
    let f : C(U.left, PadicAlgCl l) := s.down.1
    have hf : f ∈ PadicAlgCl.locallyFiniteFunctions l U.left := s.down.2
    choose N hN hfin using hf
    choose W hWN hWo hxW using fun x ↦ mem_nhds_iff.1 (hN x)
    refine (ProEt.topology X).superset_covering ?_ (ProEt.generate_ofArrows_mem_topology U
      (fun x ↦ ⟨W x, hWo x⟩) fun x ↦ ⟨x, hxW x⟩)
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨x⟩
    let g : C((ProEt.ofOpens U ⟨W x, hWo x⟩).left, PadicAlgCl l) :=
      f.comp (Scheme.Opens.ι ⟨W x, hWo x⟩).base.hom
    have hg : FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (Set.range g)) :=
      Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ_[l] (f '' N x))
        (Submodule.span_mono (by
          rintro _ ⟨y, rfl⟩
          exact ⟨_, hWN x y.2, rfl⟩))
    obtain ⟨S, q, hq⟩ := exists_finset_sum_padicAlgClBasisIndex l g hg
    refine ⟨∑ b ∈ S, DirectSum.of (fun _ ↦ (padicAbSheaf l X).obj.obj _) b (ULift.up (q b)), ?_⟩
    refine ULift.ext (Subtype.ext (ContinuousMap.ext fun t ↦ ?_))
    refine Eq.trans ?_ (hq t).symm
    let ev : (adicAbSheaf l X).obj.obj (op (ProEt.ofOpens U ⟨W x, hWo x⟩)) →+ PadicAlgCl l :=
      { toFun y := y.down.1 t
        map_zero' := rfl
        map_add' _ _ := rfl }
    refine (map_sum (ev.comp ((padicDirectSumPresheafToAdicAbSheaf l X).app _).hom) _ S).trans
      (Finset.sum_congr rfl fun b _ ↦ ?_)
    rw [AddMonoidHom.comp_apply]
    erw [DirectSum.toAddMonoid_of]
    rw [Algebra.smul_def, mul_comm]
    rfl

/-- **`ℚ̄_ℓ,X = ⨁_{b ∈ B} ℚ_ℓ,X`**: the cocone `(q ↦ b q)_{b ∈ B}` is a colimit cocone of
abelian sheaves. -/
noncomputable def isColimitAdicAbSheafCocone : IsColimit (adicAbSheafCocone l X) :=
  Sheaf.isColimitOfW _ _ (isColimitPadicDirectSumPresheafCocone l X)
    (padicDirectSumPresheafToAdicAbSheaf l X) (fun b ↦ by
      ext x
      exact DirectSum.toAddMonoid_of _ _ _)
    ((GrothendieckTopology.W_iff_isLocallyBijective _ _).2 ⟨inferInstance, inferInstance⟩)

end PadicAlgClSheaf

/-! ### The rationalization formula for `ℤ_ℓ,X` -/

section Regular

/-- On the `n`-th copy of `ℤ_ℓ,X` in the summand `b`, the rationalization comparison of `ℤ_ℓ,X`
followed by `ℚ̄_ℓ ⊗ ℤ_ℓ,X ≅ ℚ̄_ℓ,X` is `g ↦ b ℓ⁻ⁿ g`. -/
lemma rationalizationComparisonι_regular_comp (b : padicAlgClBasisIndex l) (n : ℕ) :
    rationalizationComparisonι l X (Mod.regular (padicIntAbSheaf X l)) b n ≫
      (AdicSheaf.toAb l X).map (adicSheafExtendScalarsRegularIso l X).hom =
      padicIntScaledHom l X n ≫ padicAbSheafMulHom l X b := by
  rw [rationalizationComparisonι, Category.assoc, adicScalarMul_naturality, ← Category.assoc,
    adicSheafExtendScalarsUnitAb_regular_comp, padicIntSheafToAdicConstantSheaf_eq]
  ext U x
  refine ULift.ext (Subtype.ext (ContinuousMap.ext fun t ↦ ?_))
  calc _ = ((b : PadicAlgCl l) / (l : PadicAlgCl l) ^ n) *
        algebraMap ℚ_[l] (PadicAlgCl l) (x.down t : ℚ_[l]) := rfl
    _ = (b : PadicAlgCl l) *
        algebraMap ℚ_[l] (PadicAlgCl l) (((l : ℚ_[l]) ^ n)⁻¹ * (x.down t : ℚ_[l])) := by
      rw [map_mul, map_inv₀, map_pow, map_natCast]
      ring
    _ = _ := rfl

/-- **The rationalization formula for `ℤ_ℓ,X`**: the rationalization comparison
`⨁_{b ∈ B} colim (ℤ_ℓ,X --ℓ--> ℤ_ℓ,X --ℓ--> ⋯) ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} ℤ_ℓ,X` is an isomorphism:
`colim (ℤ_ℓ,X --ℓ--> ⋯) = ℚ_ℓ,X` and `⨁_{b ∈ B} ℚ_ℓ,X = ℚ̄_ℓ,X`. -/
instance isIso_rationalizationComparison_app_regular :
    IsIso ((rationalizationComparison l X).app (Mod.regular (padicIntAbSheaf X l))) := by
  let i₁ : colimit ((ellMulTower l).obj (padicIntAbSheaf X l)) ≅ padicAbSheaf l X :=
    (colimit.isColimit _).coconePointUniqueUpToIso (isColimitPadicAbSheafCocone l X)
  let i₂ : colimit ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
      (colimit ((ellMulTower l).obj (padicIntAbSheaf X l)))) ≅ adicAbSheaf l X :=
    HasColimit.isoOfNatIso ((Functor.const _).mapIso i₁) ≪≫
      (colimit.isColimit _).coconePointUniqueUpToIso (isColimitAdicAbSheafCocone l X)
  have h : (rationalizationComparison l X).app (Mod.regular (padicIntAbSheaf X l)) ≫
      (AdicSheaf.toAb l X).map (adicSheafExtendScalarsRegularIso l X).hom = i₂.hom := by
    refine rationalizationModel_hom_ext l X fun b n ↦ ?_
    rw [rationalizationComparison_app, ι_ι_rationalizationComparisonApp_assoc,
      rationalizationComparisonι_regular_comp]
    erw [Iso.trans_hom, HasColimit.ι_isoOfNatIso_hom_assoc,
      IsColimit.comp_coconePointUniqueUpToIso_hom, Functor.mapIso_hom, Functor.const_map_app,
      IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]
    rfl
  have : IsIso ((rationalizationComparison l X).app (Mod.regular (padicIntAbSheaf X l)) ≫
      (AdicSheaf.toAb l X).map (adicSheafExtendScalarsRegularIso l X).hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((AdicSheaf.toAb l X).map
    (adicSheafExtendScalarsRegularIso l X).hom)

end Regular

end AlgebraicGeometry.ProEtale
