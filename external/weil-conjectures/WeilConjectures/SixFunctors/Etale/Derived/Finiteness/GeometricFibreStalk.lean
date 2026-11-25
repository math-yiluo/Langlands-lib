/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.GeometricFibreRank
public import WeilConjectures.AlgebraicGeometry.GeometricStalkComparisonConstant
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.StrictLocalAbelianTotalExchange
public import WeilConjectures.ConstructibleSheaf.Noetherian
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProperBaseChangeHomology
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Geometric stalks of proper direct images

For a proper morphism `f : X ⟶ S`, a geometric point `x : Spec Ω ⟶ S` (`Ω` separably closed)
and a sheaf `F` of modules over a finite ring, the stalk at `x` of `Rᵠf_* F` is the étale
cohomology `Hᵠ(X_x, F|)` of the geometric fibre
(`nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_of_isProper`,
blueprint `corollary-cohomology-geometric-fibres--2`): by proper base change it is the stalk of the
direct image along `X_x ⟶ Spec Ω`, which is computed by the strict-local exchange. For constant
coefficients `ℤ/ℓ` this gives the stalk criterion used in
`proposition-proper-direct-image-finite-coefficients`
(`isConstructibleSheaf_homology_rightDerivedLowerStar_of_sheafH_geometricFibre`).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section StrictLocal

/-- **Stalks of higher direct images over a strictly henselian local base.** Let `A` be a
henselian local ring with separably closed residue field and `h : P ⟶ Spec A`. For an abelian
étale sheaf `G` on `P`, the stalk of `Rᵠh_* G` at the closed geometric point of `Spec A` is the
étale cohomology group `Hᵠ(P, G)`. This is the identity case `A = B`, `φ = id` of the
strict-local exchange
(`AlgebraicGeometry.Etale.exists_addEquiv_strictLocal_abelian_total_exchange`).
-/
theorem nonempty_addEquiv_sheafFiber_homology_rightDerivedFunctorPlus_of_henselian
    {A : Type u} [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    {P : Scheme.{u}} (h : P ⟶ Spec (.of A)) (G : Sheaf P.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) :
    Nonempty (((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          (((h)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) ≃+ Sheaf.H G q) := by
  have hg : Spec.map (CommRingCat.ofHom (RingHom.id A)) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have sq : IsPullback (𝟙 P) h h (Spec.map (CommRingCat.ofHom (RingHom.id A))) := by
    rw [hg]
    exact IsPullback.id_horiz h
  obtain ⟨a₁, -, -⟩ := Etale.exists_addEquiv_strictLocal_abelian_total_exchange (RingHom.id A)
    h h (𝟙 P) sq G q
  let t₀ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let g := Spec.map (CommRingCat.ofHom (RingHom.id A))
  let L := ((h)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  let e₁ := ((pointSmallEtale t₀).sheafFiber (A := AddCommGrpCat.{u + 1})).mapIso
    (((g)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).app L)
  let e₂ := (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} g t₀).app
    ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj L)
  have key : Nonempty (((pointSmallEtale (t₀ ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj L) ≃+ Sheaf.H G q) :=
    ⟨(e₂.symm ≪≫ e₁).addCommGroupIsoToAddEquiv.trans a₁⟩
  have hg' : t₀ ≫ g = t₀ :=
    (congrArg (t₀ ≫ ·) hg).trans (Category.comp_id t₀)
  rw [hg'] at key
  exact key

end StrictLocal

section CoefficientChange

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The underlying abelian sheaf of a sheaf `G` of `Λ`-modules is the underlying abelian sheaf of
its restriction of scalars to `ULift ℤ`. -/
noncomputable def sheafComposeForget₂RestrictScalarsIso {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
        ((Sheaf.restrictScalars X.smallEtaleTopology (uliftIntRingHom Λ)).obj G) ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerLeft G.obj (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl :
      ModuleCat.restrictScalars.{u + 1} (uliftIntRingHom Λ) ⋙
          forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1} ≅
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))

/-- **Higher direct images of underlying abelian sheaves.** For `h : P ⟶ T` and a sheaf `G` of
`Λ`-modules on `P`, the underlying abelian sheaf of `Rᵠh_* G` is `Rᵠh_*` of the underlying abelian
sheaf of `G` (computed through restriction of scalars to `ULift ℤ`,
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`, and the equivalence of
`ULift ℤ`-module sheaves with abelian sheaves,
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarForget₂`). -/
noncomputable def forget₂HomologyRightDerivedFunctorPlusIso {P T : Scheme.{u}} (h : P ⟶ T)
    (G : Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
        ((Sheaf.restrictScalars T.smallEtaleTopology (uliftIntRingHom Λ)).obj
          ((DerivedCategory.Plus.homologyFunctor _ q).obj
            (((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ≅
      (DerivedCategory.Plus.homologyFunctor _ q).obj
        (((h)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G))) :=
  let ψ := uliftIntRingHom Λ
  let res := fun Y : Scheme.{u} ↦ Sheaf.restrictScalars Y.smallEtaleTopology ψ
  let Φ := fun Y : Scheme.{u} ↦ sheafCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  (Φ T).mapIso (((res T).mapDerivedCategoryPlusHomologyFunctorIso q).app _ ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso
        (asIso ((rightDerivedLowerStarRestrictScalars ψ h).app K) ≪≫
          ((h)_*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)]).rightDerivedFunctorPlus.mapIso
            (((res P).mapDerivedCategoryPlusSingleFunctor 0).app G))) ≪≫
    ((Φ T).mapDerivedCategoryPlusHomologyFunctorIso q).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((rightDerivedLowerStarForget₂ h).app _) ≪≫
        ((h)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlus.mapIso
          (((Φ P).mapDerivedCategoryPlusSingleFunctor 0).app _ ≪≫
            (DerivedCategory.Plus.singleFunctor _ 0).mapIso
              (sheafComposeForget₂RestrictScalarsIso G)))

/-- The stalk of a sheaf of `Λ`-modules and the stalk of its underlying abelian sheaf, after
restriction of scalars to `ULift ℤ`, are the same abelian group. -/
noncomputable def sheafFiberForget₂RestrictScalarsAddEquiv {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj N ≃+
      ((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
          ((Sheaf.restrictScalars T.smallEtaleTopology (uliftIntRingHom Λ)).obj N)) :=
  have : LocallySmall.{u} T.Etale := locallySmall_self _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  ((((pointSmallEtale t).sheafFiberCompIso
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app N).symm ≪≫
    ((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).mapIso
      (sheafComposeForget₂RestrictScalarsIso N).symm).addCommGroupIsoToAddEquiv

end CoefficientChange

section GeometricFibre

/-- For `h : P ⟶ Spec A` over a strictly henselian local ring `A` and a sheaf `G` of
`Λ`-modules on `P`, the stalk of `Rᵠh_* G` at the closed geometric point of `Spec A` is
`Hᵠ(P, G)`, the étale cohomology of the underlying abelian sheaf of `G`. -/
theorem nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_of_henselian
    {Λ : Type (u + 1)} [CommRing Λ]
    {A : Type u} [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    {P : Scheme.{u}} (h : P ⟶ Spec (.of A)) (G : Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℕ) :
    Nonempty (((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
          ((R((h)_*[ModuleCat.{u + 1} Λ])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
          q) := by
  obtain ⟨a⟩ := nonempty_addEquiv_sheafFiber_homology_rightDerivedFunctorPlus_of_henselian h
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q
  let t := pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  let e₁ := (t.sheafFiber (A := ModuleCat.{u + 1} Λ)).mapIso
    ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      (((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app K).symm)
  let e₂ := (t.sheafFiber (A := AddCommGrpCat.{u + 1})).mapIso
    (forget₂HomologyRightDerivedFunctorPlusIso h G q)
  exact ⟨e₁.toLinearEquiv.toAddEquiv.trans
    ((sheafFiberForget₂RestrictScalarsAddEquiv _ _).trans
      (e₂.addCommGroupIsoToAddEquiv.trans a))⟩

/-- The residue field of a separably closed field is separably closed. -/
instance isSepClosed_residueField_of_isSepClosed (Ω : Type*) [Field Ω] [IsSepClosed Ω] :
    IsSepClosed (IsLocalRing.ResidueField Ω) :=
  have := IsFractionRing.idem Ω
  IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing Ω

/-- Blueprint `corollary-cohomology-geometric-fibres--2`: Finite-coefficient geometric-fiber
formula.

Let `f : X ⟶ S` be proper, `x : Spec Ω ⟶ S` a geometric point, `X_x = X ×_S Spec Ω` the
geometric fibre with projection `i : X_x ⟶ X`, and `Λ` a finite ring. For every sheaf `F` of
`Λ`-modules on `X` and `q ≥ 0`, the stalk `(Rᵠf_* F)_x` is the étale cohomology group
`Hᵠ(X_x, i^* F)`. -/
theorem nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_of_isProper
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    Nonempty (((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
        ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((pullback.fst f x)^*[ModuleCat.{u + 1} Λ].obj F)) q) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let t₀ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue Ω))
  obtain ⟨β, -⟩ := Scheme.exists_geometricStalkComparison_constant (Λ := Λ) (t₀ ≫ x) x
    (congrArg x (Subsingleton.elim _ _))
  obtain ⟨a⟩ := nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_of_henselian
    (pullback.snd f x) ((pullback.fst f x)^*[ModuleCat.{u + 1} Λ].obj F) q
  let M := (_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
    ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))
  let e := β.symm.app M ≪≫ ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) x t₀).app M).symm ≪≫
    ((pointSmallEtale t₀).sheafFiber (A := ModuleCat.{u + 1} Λ)).mapIso
      (upperStarHomologyRightDerivedLowerStarIsoOfIsProper (IsPullback.of_hasPullback f x) F q)
  exact ⟨e.toLinearEquiv.toAddEquiv.trans a⟩

end GeometricFibre

section ConstantCoefficients

/-- Isomorphic abelian étale sheaves have isomorphic cohomology groups. -/
noncomputable def sheafHAddEquivOfIso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (n : ℕ) :
    Sheaf.H F n ≃+ Sheaf.H G n where
  toFun := Sheaf.H.map e.hom n
  invFun := Sheaf.H.map e.inv n
  left_inv x := by
    rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  right_inv x := by
    rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]
  map_add' := map_add _

/-- The underlying abelian sheaf of the pullback `i^* (ℤ/ℓ)_X` of the constant sheaf of
`ℤ/ℓ`-modules is the constant abelian sheaf `ℤ/ℓ` on `X'`. -/
noncomputable def sheafComposeForget₂UpperStarConstantSheafIso (ℓ : ℕ) {X' X : Scheme.{u}}
    (i : X' ⟶ X) :
    (sheafCompose _
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) AddCommGrpCat.{u + 1})).obj
      ((i)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))) ≅ X'.constantZMod ℓ :=
  have : X'.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  (sheafCompose _ _).mapIso ((constantSheafCompUpperStarIso _ i).app _) ≪≫
    (constantCommuteCompose X'.smallEtaleTopology _).app _

/-- Blueprint `corollary-cohomology-geometric-fibres--2`, for the constant sheaf `ℤ/ℓ`: for
`f : X ⟶ S` proper and a point `s` of `S`, the stalk of `Rʳf_*(ℤ/ℓ)` at the geometric point
`Spec κ(s)‾ ⟶ S` is the étale cohomology group `Hʳ(X_{s̄}, ℤ/ℓ)` of the geometric fibre
`X_{s̄} = X ×_S Spec κ(s)‾`. -/
theorem nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_constantSheaf
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (ℓ : ℕ) [NeZero ℓ] (s : S) (r : ℕ) :
    Nonempty (((pointSmallEtale (S.algClosurePoint s)).sheafFiber
        (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
        ((_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).obj
          ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              ((constantSheaf X.smallEtaleTopology
                (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
                  (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))) ≃+
      Sheaf.H ((Limits.pullback f (S.geometricPointAt s)).constantZMod ℓ) r) := by
  obtain ⟨a⟩ := nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_of_isProper f
    (S.algClosurePoint s) ((constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))) r
  exact ⟨a.trans (sheafHAddEquivOfIso
    (sheafComposeForget₂UpperStarConstantSheafIso ℓ (pullback.fst f (S.algClosurePoint s))) r)⟩

/-- The cardinality form of
`AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_constantSheaf`:
`|(Rʳf_*(ℤ/ℓ))_{s̄}| = |Hʳ(X_{s̄}, ℤ/ℓ)|` for `f` proper. -/
theorem natCard_sheafFiber_homology_rightDerivedLowerStar_constantSheaf
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (ℓ : ℕ) [NeZero ℓ] (s : S) (r : ℕ) :
    Nat.card (((pointSmallEtale (S.algClosurePoint s)).sheafFiber
        (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
        ((_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).obj
          ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              ((constantSheaf X.smallEtaleTopology
                (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
                  (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))))) =
      Nat.card (Sheaf.H ((Limits.pullback f (S.geometricPointAt s)).constantZMod ℓ) r) :=
  have ⟨a⟩ := nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_constantSheaf f ℓ s r
  Nat.card_congr a.toEquiv

/-- **Constructibility of proper direct images from the geometric fibres.** Let `S` be
Noetherian, `f : X ⟶ S` proper and `r : ℤ`. Suppose that the groups `Hʳ(X_{s̄}, ℤ/ℓ)` of the
geometric fibres `X_{s̄} = X ×_S Spec κ(s)‾` are finite, and that for every `n ≥ 1` the set of
points `s` with `|Hʳ(X_{s̄}, ℤ/ℓ)| = n` is constructible. Then `Rʳf_*(ℤ/ℓ)` is constructible.
(For `r < 0` the hypotheses concern `H⁰` and the conclusion holds trivially.)

By proper base change the stalks of `Rʳf_*(ℤ/ℓ)` are the groups `Hʳ(X_{s̄}, ℤ/ℓ)`
(`nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_constantSheaf`),
and the stalk criterion `AlgebraicGeometry.Scheme.isConstructibleSheaf_iff_isConstructible_card`
applies. This is the final step of the blueprint proof of
`proposition-proper-direct-image-finite-coefficients`. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_of_sheafH_geometricFibre
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f] (ℓ : ℕ) [NeZero ℓ] (r : ℤ)
    (hfin : ∀ s : S,
      Finite (Sheaf.H ((Limits.pullback f (S.geometricPointAt s)).constantZMod ℓ) r.toNat))
    (hcons : ∀ n : ℕ, 1 ≤ n → Topology.IsConstructible {s : S |
      Nat.card (Sheaf.H ((Limits.pullback f (S.geometricPointAt s)).constantZMod ℓ) r.toNat) =
        n}) :
    IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ r).obj
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))) := by
  rcases lt_or_ge r 0 with hr | hr
  · have := ((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))]
      ).isGE_rightDerivedFunctor_obj_singleFunctor
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
        (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))
    exact IsConstructibleSheaf.of_isZero (_root_.DerivedCategory.isZero_of_isGE _ 0 r hr)
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  simp only [Int.toNat_natCast] at hfin hcons
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hiso := nonempty_addEquiv_sheafFiber_homology_rightDerivedLowerStar_constantSheaf f ℓ
  have : IsFiniteSheaf ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).obj
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))) := by
    refine ⟨fun Ω _ _ t ↦ ?_⟩
    let s := t (IsLocalRing.closedPoint Ω)
    obtain ⟨β, -⟩ := Scheme.exists_geometricStalkComparison_constant
      (Λ := ULift.{u + 1} (ZMod ℓ)) t (S.algClosurePoint s)
      (Scheme.algClosurePoint_base _ _ _).symm
    obtain ⟨a⟩ := hiso s n
    have := hfin s
    have : Finite (((pointSmallEtale t).sheafFiber
        (A := ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj _) :=
      Finite.of_equiv _ ((β.app _).toLinearEquiv.toEquiv.trans a.toEquiv).symm
    exact (ModuleCat.isFinitelyGenerated_iff _).2 Module.Finite.of_finite
  rw [Scheme.isConstructibleSheaf_iff_isConstructible_card]
  intro m hm
  convert hcons m hm using 1
  ext s
  obtain ⟨a⟩ := hiso s n
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Nat.card_congr a.toEquiv]

end ConstantCoefficients

end Etale

end AlgebraicGeometry
