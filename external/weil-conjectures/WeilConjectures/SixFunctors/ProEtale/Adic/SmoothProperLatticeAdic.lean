/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeModule
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalizationFree
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalizationRegular
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetAbRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar

/-!
# Higher direct images of `ℓ`-adic lattice sheaves along smooth proper morphisms

Let `K` be a field, `Y` locally of finite type over `K`, `f : X ⟶ Y` smooth and proper and
`(Gₙ)` an `ℓ`-adic tower of étale sheaves of `ULift ℤ_ℓ`-modules on `X` as in
`WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeModule`, with limit `M` (in
`ℤ_ℓ,X`-modules) of the transported tower `ν^* Gₙ`. For an `ℓ`-adic sheaf `F ≅ ℚ̄_ℓ ⊗ M`, every
`Hⁿ(Rf_* F[0])` is lisse
(`isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_lattice`).
This is the *lattice case* of
`isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper`.

For `Y` connected and quasi-compact
(`isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_lattice_of_connectedSpace`),
it is deduced from the integral statement
`isAdicLisseSheaf_adicSheafExtendScalars_homology_rightDerivedPadicIntModPushforward_limit`
using the compatibility of extension of scalars with `Rf_*`
(`isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_rationalization`). In general,
`Y` is covered by connected quasi-compact opens `U`
(`Scheme.exists_isOpenImmersion_connectedSpace_compactSpace`),
over which `Rf_*` is computed on `f⁻¹ U` by open base change, and the tower restricts to `f⁻¹ U`
(`padicIntModUpperStarLimitComparisonPadicIntModTowerIso`).

The rationalization formula (`IsIso (rationalizationComparison l X)`, the comparison
`⨁_B colim (M --ℓ--> M --ℓ--> ⋯) ⟶ ℚ̄_ℓ ⊗ M`) holds on every scheme
(`isIso_rationalizationComparison_of_regular` and `isIso_rationalizationComparison_app_regular`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.AdicTowerStructure

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D] {G : ℕᵒᵖ ⥤ C}
  {ℓ : ℕ}

/-- **Exact functors preserve `ℓ`-adic tower structures**: the image of an `ℓ`-adic tower under
an exact additive functor `Φ` is an `ℓ`-adic tower, with structure maps `Φ (ιₙₘ)`. -/
def map (A : AdicTowerStructure G ℓ) (Φ : C ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] : AdicTowerStructure (G ⋙ Φ) ℓ where
  ι n m := Φ.map (A.ι n m)
  map_ι n m := by
    rw [Functor.comp_map, ← Φ.map_comp, A.map_ι, Φ.map_nsmul, Φ.map_id]
    rfl
  ι_map n m := by rw [Functor.comp_map, ← Φ.map_comp, A.ι_map, Φ.map_zero]
  shortExact n m := (A.shortExact n m).map_of_exact Φ

end CategoryTheory.AdicTowerStructure

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {l : ℕ} [Fact l.Prime]

/-- **The lattice case of lisse direct images along smooth proper morphisms**, for `Y` connected
and quasi-compact of finite type over a field `K`, granting the rationalization formula on `X`
and on `Y`: if `F ≅ ℚ̄_ℓ ⊗ M` where `M` is the limit of the transport to `ℤ_ℓ,X`-modules of an
`ℓ`-adic tower of finite locally constant étale sheaves of torsion `ℤ_ℓ`-modules, every
`Hⁿ(Rf_* F[0])` is a lisse `ℓ`-adic sheaf. -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_lattice_of_connectedSpace
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] [ConnectedSpace Y] (f : X ⟶ Y) [Smooth f] [IsProper f]
    [IsIso (rationalizationComparison l X)] [IsIso (rationalizationComparison l Y)]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])))
    (A : AdicTowerStructure G l) (I : ℕ → Ideal (ULift.{u + 1} ℤ_[l]))
    [∀ n, Finite (ULift.{u + 1} ℤ_[l] ⧸ I n)]
    [∀ n, HasInvertibleExponent (ULift.{u + 1} ℤ_[l] ⧸ I n) (Spec (.of K))]
    (F₀ : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l] ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F₀ n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F₀ n))
    {F : AdicSheaf l X} (eF : F ≅ (adicSheafExtendScalars X l).obj (limit
      (comparisonPadicIntModTower X l G (zsmul_id_eq_zero_of_adicTowerStructure X l A))))
    (n : ℤ) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine IsAdicLisseSheaf.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((f)_*ᵃ[l].rightDerivedFunctor.mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso eF.symm))) ?_
    exact isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_rationalization l f _ q
      (isAdicLisseSheaf_adicSheafExtendScalars_homology_rightDerivedPadicIntModPushforward_limit
        l aY f G A I F₀ eG q)
  · exact isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_neg l f F hn

/-! ### Restriction of étale `ℓ`-adic towers -/

section Restriction

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The abelian sheaf underlying `ν^*` commutes with pullback along a weakly étale morphism
`g : W ⟶ X`: `g^* (ν_X^* G)_ab ≅ (ν_W^* g^* G)_ab`. -/
noncomputable def comparisonUpperStarAbCompUpperStarIso {X W : Scheme.{u}} (g : W ⟶ X)
    [h : WeaklyEtale g] :
    comparisonUpperStarAb Λ X ⋙ (g)^*[Ab.{u + 1}] ≅
      Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙ comparisonUpperStarAb Λ W :=
  Functor.isoWhiskerLeft (comparisonUpperStarAb Λ X)
      (upperStarIsoLocalizationRestriction Ab.{u + 1} g h) ≪≫
    (Iso.refl _ : _ ≅ (comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙
      localizationRestriction (ModuleCat.{u + 1} Λ) g h) ⋙
        sheafCompose (ProEt.topology W) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
      (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) g h).symm ≪≫
      comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g) _ ≪≫
    Functor.associator _ _ _

variable (l) in
/-- **Pullback of the limit of a transported tower**: for a weakly étale monomorphism
`g : W ⟶ X` (e.g. an open immersion) and an étale tower `(Gₙ)` of sheaves of `Λ`-modules with
`ℓⁿ Gₙ = 0`, the pullback of `lim ν^* Gₙ`, as `ℤ_ℓ`-modules, is the limit of the transported
tower of `(g^* Gₙ)`. Pullback along `g` preserves limits, being restriction along the
localization functor, and the isomorphism of underlying abelian sheaves is automatically linear
(`ProEtale.padicIntModIsoLimitOfForgetIso`). -/
noncomputable def padicIntModUpperStarLimitComparisonPadicIntModTowerIso {X W : Scheme.{u}}
    (g : W ⟶ X) [h : WeaklyEtale g] [Mono g]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0)
    (hG' : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) •
      𝟙 ((G ⋙ Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj (op n)) = 0) :
    (padicIntModUpperStar l g).obj (limit (comparisonPadicIntModTower X l G hG)) ≅
      limit (comparisonPadicIntModTower W l (G ⋙ Etale.upperStar (ModuleCat.{u + 1} Λ) g)
        hG') :=
  have : PreservesLimitsOfSize.{0, 0} (g)^*[Ab.{u + 1}] :=
    preservesLimits_of_natIso (upperStarIsoLocalizationRestriction Ab.{u + 1} g h).symm
  padicIntModIsoLimitOfForgetIso (zsmul_id_comparisonPadicIntModTower_obj_X l _ _)
    ((g)^*[Ab.{u + 1}].mapIso (preservesLimitIso (Mod.forget _) _) ≪≫
      preservesLimitIso (g)^*[Ab.{u + 1}] _ ≪≫
      HasLimit.isoOfNatIso (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft G (comparisonUpperStarAbCompUpperStarIso g) ≪≫
        (Functor.associator _ _ _).symm : _ ≅ comparisonPadicIntModTower W l
          (G ⋙ Etale.upperStar (ModuleCat.{u + 1} Λ) g) hG' ⋙ Mod.forget _) ≪≫
      (preservesLimitIso (Mod.forget _) _).symm)

end Restriction

/-- Every point of a locally Noetherian scheme `Y` lies in the image of an open immersion from a
connected quasi-compact scheme: the connected component of the point in an affine open
neighbourhood, which is open since `Y` is locally connected, and closed in the affine open. -/
lemma _root_.AlgebraicGeometry.Scheme.exists_isOpenImmersion_connectedSpace_compactSpace
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (y : Y) :
    ∃ (U : Scheme.{u}) (j : U ⟶ Y), IsOpenImmersion j ∧ ConnectedSpace U ∧ CompactSpace U ∧
      y ∈ Set.range j := by
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  have : IsAffine V := hV
  let C : V.toScheme.Opens := ⟨connectedComponent ⟨y, hyV⟩, isOpen_connectedComponent⟩
  refine ⟨C.toScheme, C.ι ≫ V.ι, inferInstance,
    Subtype.connectedSpace isConnected_connectedComponent,
    isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact,
    ⟨⟨⟨y, hyV⟩, mem_connectedComponent⟩, rfl⟩⟩

/-- **The lattice case of lisse direct images along smooth proper morphisms**, for `Y` locally
of finite type over a field `K`: if
`F ≅ ℚ̄_ℓ ⊗ M` where `M` is the limit of the transport to `ℤ_ℓ,X`-modules of an `ℓ`-adic tower
of finite locally constant étale sheaves of torsion `ℤ_ℓ`-modules, every `Hⁿ(Rf_* F[0])` is a
lisse `ℓ`-adic sheaf. Being lisse is local on `Y`, which is covered by connected quasi-compact
opens `U`; over `U`, `Rf_*` is computed on `f⁻¹ U` (open base change), to which the tower
restricts, and
`isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_lattice_of_connectedSpace`
applies. -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_lattice
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    (f : X ⟶ Y) [Smooth f] [IsProper f]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])))
    (A : AdicTowerStructure G l) (I : ℕ → Ideal (ULift.{u + 1} ℤ_[l]))
    [∀ n, Finite (ULift.{u + 1} ℤ_[l] ⧸ I n)]
    [∀ n, HasInvertibleExponent (ULift.{u + 1} ℤ_[l] ⧸ I n) (Spec (.of K))]
    (F₀ : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l] ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F₀ n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F₀ n))
    {F : AdicSheaf l X} (eF : F ≅ (adicSheafExtendScalars X l).obj (limit
      (comparisonPadicIntModTower X l G (zsmul_id_eq_zero_of_adicTowerStructure X l A))))
    (n : ℤ) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  have := LocallyOfFiniteType.isLocallyNoetherian aY
  have hrat : ∀ Z : Scheme.{u}, IsIso (rationalizationComparison l Z) := fun Z ↦
    isIso_rationalizationComparison_of_regular l Z inferInstance
  choose U j hj hU hU' hy using Scheme.exists_isOpenImmersion_connectedSpace_compactSpace (Y := Y)
  refine IsAdicLisseSheaf.of_cover j (Scheme.zariskiPrecoverage_le_proetalePrecoverage _
    ((Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).2
      ⟨fun y ↦ ⟨y, hy y⟩, hj⟩)) fun y ↦ ?_
  have := hj y
  have := hU y
  have : QuasiCompact (j y ≫ aY) := HasAffineProperty.iff_of_isAffine.mpr (hU' y)
  have := hrat (pullback f (j y))
  have := hrat (U y)
  let g := pullback.fst f (j y)
  let G' := G ⋙ Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) g
  let A' : AdicTowerStructure G' l := A.map _
  have (k : ℕ) : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l] ⧸ I k)) g).obj (F₀ k)) :=
    IsFiniteLocallyConstantSheaf.upperStar g (F₀ k)
  refine (isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_lattice_of_connectedSpace
    (j y ≫ aY)
    (pullback.snd f (j y)) G' A' I _
    (fun k ↦ (Etale.upperStar _ g).mapIso (eG k) ≪≫
      (Etale.upperStarRestrictScalarsIso (Ideal.Quotient.mk (I k)) g).app (F₀ k))
    ((g)^*ᵃ[l].mapIso eF ≪≫
      ((padicIntModUpperStarCompAdicSheafExtendScalarsIso l g).app _).symm ≪≫
      (adicSheafExtendScalars _ l).mapIso
        (padicIntModUpperStarLimitComparisonPadicIntModTowerIso l g G _ _)) n).of_iso ?_
  exact (DerivedCategory.homologyFunctor _ n).mapIso
      (mapDerivedCategoryUpperStarRightDerivedFunctorLowerStarIso f (j y) F).symm ≪≫
    (((j y)^*ᵃ[l].mapDerivedCategoryHomologyFunctorIso n).app _).symm

end AlgebraicGeometry.ProEtale
