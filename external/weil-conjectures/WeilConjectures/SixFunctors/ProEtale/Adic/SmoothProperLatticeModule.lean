/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeLimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.ModuleForgetAbRightDerivedLowerStar

/-!
# Higher direct images of limits of `ℓ`-adic towers as `ℤ_ℓ`-modules

Let `K` be a field, `Y` of finite type over `K`, `f : X ⟶ Y` smooth and proper and `(Gₙ)` an
`ℓ`-adic tower of étale sheaves of `ULift ℤ_ℓ`-modules on `X` as in
`WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeLisse`. Let `M` be the limit, in
`ℤ_ℓ,X`-modules, of the transported tower `ν^* Gₙ`, and `Mₙ` the transport to `ℤ_ℓ,Y`-modules of
`Rʲf_* Gₙ`. We show that
```
Hʲ(Rf_* M[0]) ≅ lim Mₙ
```
as `ℤ_ℓ,Y`-modules, the left hand side being computed with the derived pushforward of
`ℤ_ℓ`-modules `AlgebraicGeometry.ProEtale.padicIntModPushforward`
(`AlgebraicGeometry.ProEtale.homologyRightDerivedPadicIntModPushforwardLimitIso`). Consequently,
for `Y` connected, `ℚ̄_ℓ ⊗ Hʲ(Rf_* M[0])` is lisse
(`isAdicLisseSheaf_adicSheafExtendScalars_homology_rightDerivedPadicIntModPushforward_limit`).

The isomorphism of underlying abelian sheaves comes from
`AlgebraicGeometry.ProEtale.homologyRightDerivedLowerStarLimitIso`, the comparisons of derived
pushforwards with underlying abelian sheaves, and the identification of the underlying abelian
sheaf of `M` with that of `lim ν^* Gₙ`
(`AlgebraicGeometry.ProEtale.forgetLimitComparisonPadicIntModTowerIso`). It is automatically
`ℤ_ℓ,Y`-linear: every additive map into the limit of a tower of `ℤ_ℓ,Y`-modules `Tₙ` killed by
`ℓⁿ` is linear (`AlgebraicGeometry.ProEtale.padicInt_act_comp_eq_of_limit`), the limit being
`ℓ`-adically separated.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory Abelian.hasFiniteBiproducts

section Linear

variable {X : Scheme.{u}} {l : ℕ} [Fact l.Prime]

/-- **Additive maps into limits of `ℓ`-adic towers of `ℤ_ℓ,X`-modules are `ℤ_ℓ,X`-linear**: if
the `n`-th term of a tower `T` of `ℤ_ℓ,X`-modules is killed by `ℓⁿ`, every morphism of abelian
sheaves `M ⟶ lim T` from a `ℤ_ℓ,X`-module commutes with the actions, `lim T` being `ℓ`-adically
separated. -/
lemma padicInt_act_comp_eq_of_limit
    {T : ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)}
    (hT : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (T.obj (op n)).X = 0)
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)}
    (φ : M.X ⟶ (limit T).X) :
    Mod.act M.X ≫ φ = padicIntAbSheaf X l ◁ φ ≫ Mod.act (limit T).X :=
  Mod.act_comp_eq_of_epi φ (fun n : ℕ ↦ ((l ^ n : ℕ) : ℤ))
    (fun _ ↦ Functor.map_epi (tensorRight M.X) _) (fun n ↦ (limit.π T (op n)).hom)
    (fun n ↦ by simpa [Preadditive.comp_zsmul] using (limit.π T (op n)).hom ≫= hT n)
    (fun g hg ↦ (isLimitOfPreserves (Mod.forget _) (limit.isLimit T)).hom_ext fun ⟨n⟩ ↦ by
      simpa using hg n)

/-- **Isomorphisms of abelian sheaves onto limits of `ℓ`-adic towers are `ℤ_ℓ,X`-linear**: an
isomorphism of underlying abelian sheaves `M ≅ lim T`, where the `n`-th term of the tower `T` of
`ℤ_ℓ,X`-modules is killed by `ℓⁿ`, is an isomorphism of `ℤ_ℓ,X`-modules. -/
noncomputable def padicIntModIsoLimitOfForgetIso
    {T : ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)}
    (hT : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (T.obj (op n)).X = 0)
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)}
    (e : M.X ≅ (limit T).X) : M ≅ limit T :=
  Mod.isoMk e (padicInt_act_comp_eq_of_limit hT e.hom)

/-- The isomorphism `ProEtale.padicIntModIsoLimitOfForgetIso hT e` has underlying morphism of
abelian sheaves `e`. -/
@[simp]
lemma padicIntModIsoLimitOfForgetIso_hom_hom
    {T : ℕᵒᵖ ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)}
    (hT : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (T.obj (op n)).X = 0)
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)}
    (e : M.X ≅ (limit T).X) : (padicIntModIsoLimitOfForgetIso hT e).hom.hom = e.hom :=
  rfl

end Linear

variable {Λ : Type (u + 1)} [CommRing Λ] (l : ℕ) [Fact l.Prime]

/-- **The underlying abelian sheaf of the limit of a transported tower**: for an étale tower
`(Gₙ)` of sheaves of `Λ`-modules with `ℓⁿ Gₙ = 0`, the underlying abelian sheaf of the limit, in
`ℤ_ℓ,X`-modules, of the transported tower `ProEtale.comparisonPadicIntModTower` is that of the
limit `lim ν^* Gₙ` of pro-étale sheaves of `Λ`-modules. -/
noncomputable def forgetLimitComparisonPadicIntModTowerIso {X : Scheme.{u}}
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0) :
    (Mod.forget _).obj (limit (comparisonPadicIntModTower X l G hG)) ≅
      (sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).obj
        (limit (G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ])) :=
  preservesLimitIso (Mod.forget _) _ ≪≫
    (preservesLimitIso (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})) (G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ])).symm

/-- The terms of the transported tower `ProEtale.comparisonPadicIntModTower X l G hG` are killed
levelwise: `ℓⁿ ν^* Gₙ = 0`. -/
lemma zsmul_id_comparisonPadicIntModTower_obj_X {X : Scheme.{u}}
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0) (n : ℕ) :
    ((l ^ n : ℕ) : ℤ) • 𝟙 ((comparisonPadicIntModTower X l G hG).obj (op n)).X = 0 :=
  zsmul_id_comparisonUpperStarAb_obj_eq_zero (hG n)

/-- **`Hʲ(Rf_* (lim ν^* Gₙ)) ≅ lim Mₙ` on underlying abelian sheaves, for towers of
`Λ`-modules**: for an `ℓ`-adic tower `(Gₙ)` of étale sheaves of `Λ`-modules, `Λ` flat over `ℤ`,
with the hypotheses of `ProEtale.homologyRightDerivedLowerStarLimitIso`, `Hʲ` of the derived
pushforward of abelian sheaves of the underlying abelian sheaf of the limit of the transported
tower `ν^* Gₙ` is the underlying abelian sheaf of the limit of the transported tower `Mₙ` of
`Rʲf_*^{ét} Gₙ`.

Stating it for a general `Λ` keeps the ring instances of all intermediate objects syntactically
equal; for `Λ = ULift ℤ_ℓ` this avoids expensive kernel conversions between `ULift.ring` and
`CommRing.toRing`. -/
noncomputable def homologyRightDerivedLowerStarForgetLimitComparisonIso [Module.Flat ℤ Λ]
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [Smooth f] [IsProper f]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (A : AdicTowerStructure G l)
    (I : ℕ → Ideal Λ) [∀ n, Finite (Λ ⧸ I n)] [∀ n, HasInvertibleExponent (Λ ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (j : ℕ) :
    (DerivedCategory.homologyFunctor _ j).obj (((f)_*[Ab.{u + 1}]).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((Mod.forget _).obj
          (limit (comparisonPadicIntModTower X l G
            (zsmul_id_eq_zero_of_adicTowerStructure X l A)))))) ≅
      (limit (comparisonPadicIntModTower Y l
        (G ⋙ DerivedCategory.singleFunctor _ 0 ⋙ R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙
          DerivedCategory.homologyFunctor _ j)
        (zsmul_id_homology_rightDerivedLowerStar_eq_zero l f A j))).X :=
  (DerivedCategory.homologyFunctor _ j).mapIso (((f)_*[Ab.{u + 1}]).rightDerivedFunctor.mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso
        (forgetLimitComparisonPadicIntModTowerIso l G _))) ≪≫
    (sheafComposeForget₂HomologyRightDerivedLowerStarIso _ f _ j).symm ≪≫
    (sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).mapIso
      (homologyRightDerivedLowerStarLimitIso aY f G I F eG (fun n ↦ A.epi_map n.le_succ) j) ≪≫
    preservesLimitIso
      (sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})) _ ≪≫
    (limit.isLimit (comparisonPadicIntModTower Y l
        (G ⋙ DerivedCategory.singleFunctor _ 0 ⋙ R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f) ⋙
          DerivedCategory.homologyFunctor _ j)
        (zsmul_id_homology_rightDerivedLowerStar_eq_zero l f A j) ⋙
          Mod.forget _)).conePointUniqueUpToIso
      (isLimitOfPreserves (Mod.forget _) (limit.isLimit _))

/-- **`Hʲ(Rf_* (lim ν^* Gₙ)) ≅ lim Mₙ` on underlying abelian sheaves**, for the derived
pushforward of `ℤ_ℓ`-modules: in the situation of
`ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit_homology_rightDerivedLowerStar`, the
underlying abelian sheaf of `Hʲ(Rf_* M[0])`, where `M` is the limit in `ℤ_ℓ,X`-modules of the
transported tower `ν^* Gₙ`, is that of the limit of the transported tower `Mₙ` of
`Rʲf_*^{ét} Gₙ`. -/
noncomputable def forgetHomologyRightDerivedPadicIntModPushforwardLimitIso
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [Smooth f] [IsProper f]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])))
    (A : AdicTowerStructure G l) (I : ℕ → Ideal (ULift.{u + 1} ℤ_[l]))
    [∀ n, Finite (ULift.{u + 1} ℤ_[l] ⧸ I n)]
    [∀ n, HasInvertibleExponent (ULift.{u + 1} ℤ_[l] ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l] ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (j : ℕ) :
    (Mod.forget _).obj ((DerivedCategory.homologyFunctor _ j).obj
        ((padicIntModPushforward l f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj (limit (comparisonPadicIntModTower X l G
            (zsmul_id_eq_zero_of_adicTowerStructure X l A)))))) ≅
      (limit (comparisonPadicIntModTower Y l
        (G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
          R(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f) ⋙
            DerivedCategory.homologyFunctor _ j)
        (zsmul_id_homology_rightDerivedLowerStar_eq_zero l f A j))).X :=
  forgetHomologyRightDerivedPadicIntModPushforwardIso l f _ j ≪≫
    homologyRightDerivedLowerStarForgetLimitComparisonIso l aY f G A I F eG j

/-- **`Hʲ(Rf_* M[0]) ≅ lim Mₙ` as `ℤ_ℓ,Y`-modules**: in the situation of
`ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit_homology_rightDerivedLowerStar`, let
`M` be the limit in `ℤ_ℓ,X`-modules of the transported tower `ν^* Gₙ` and `Mₙ` the transported
tower of `Rʲf_*^{ét} Gₙ`. Then `Hʲ(Rf_* M[0])`, computed with the derived pushforward of
`ℤ_ℓ`-modules, is isomorphic to `lim Mₙ`. The isomorphism of underlying abelian sheaves
`ProEtale.forgetHomologyRightDerivedPadicIntModPushforwardLimitIso` is automatically linear,
`lim Mₙ` being `ℓ`-adically separated. -/
noncomputable def homologyRightDerivedPadicIntModPushforwardLimitIso
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [Smooth f] [IsProper f]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])))
    (A : AdicTowerStructure G l) (I : ℕ → Ideal (ULift.{u + 1} ℤ_[l]))
    [∀ n, Finite (ULift.{u + 1} ℤ_[l] ⧸ I n)]
    [∀ n, HasInvertibleExponent (ULift.{u + 1} ℤ_[l] ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l] ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (j : ℕ) :
    (DerivedCategory.homologyFunctor _ j).obj
        ((padicIntModPushforward l f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj (limit (comparisonPadicIntModTower X l G
            (zsmul_id_eq_zero_of_adicTowerStructure X l A))))) ≅
      limit (comparisonPadicIntModTower Y l
        (G ⋙ DerivedCategory.singleFunctor _ 0 ⋙
          R(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f) ⋙
            DerivedCategory.homologyFunctor _ j)
        (zsmul_id_homology_rightDerivedLowerStar_eq_zero l f A j)) :=
  padicIntModIsoLimitOfForgetIso
    (zsmul_id_comparisonPadicIntModTower_obj_X l _ _)
    (forgetHomologyRightDerivedPadicIntModPushforwardLimitIso l aY f G A I F eG j)

/-- **`ℚ̄_ℓ ⊗ Hʲ(Rf_* M[0])` is lisse**: in the situation of
`ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit_homology_rightDerivedLowerStar`, with
`M` the limit in `ℤ_ℓ,X`-modules of the transported tower `ν^* Gₙ`, the rationalisation of the
`ℤ_ℓ,Y`-module `Hʲ(Rf_* M[0])`, computed with the derived pushforward of `ℤ_ℓ`-modules, is a
lisse `ℓ`-adic sheaf. -/
theorem isAdicLisseSheaf_adicSheafExtendScalars_homology_rightDerivedPadicIntModPushforward_limit
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] [ConnectedSpace Y] (f : X ⟶ Y) [Smooth f] [IsProper f]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])))
    (A : AdicTowerStructure G l) (I : ℕ → Ideal (ULift.{u + 1} ℤ_[l]))
    [∀ n, Finite (ULift.{u + 1} ℤ_[l] ⧸ I n)]
    [∀ n, HasInvertibleExponent (ULift.{u + 1} ℤ_[l] ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l] ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (j : ℕ) :
    IsAdicLisseSheaf ((adicSheafExtendScalars Y l).obj ((DerivedCategory.homologyFunctor _ j).obj
      ((padicIntModPushforward l f).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj (limit (comparisonPadicIntModTower X l G
          (zsmul_id_eq_zero_of_adicTowerStructure X l A))))))) :=
  IsAdicLisseSheaf.of_iso ((adicSheafExtendScalars Y l).mapIso
      (homologyRightDerivedPadicIntModPushforwardLimitIso l aY f G A I F eG j).symm)
    (isAdicLisseSheaf_adicSheafExtendScalars_limit_homology_rightDerivedLowerStar l aY f G A I F
      eG j)

end AlgebraicGeometry.ProEtale
