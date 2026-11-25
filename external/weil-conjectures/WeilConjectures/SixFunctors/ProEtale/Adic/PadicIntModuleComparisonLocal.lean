/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleComparison
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntLatticeLisse
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowGLLift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Local triviality of pro-étale towers of `ℤ_ℓ,X`-modules coming from free `ℤ/ℓⁿ`-sheaves

Let `F` be a sheaf of `Λ`-modules on `X_proét` and `gᵢ : Wᵢ ⟶ X` a pro-étale cover such that each
pullback `gᵢ^* F` is the constant sheaf of a `Λ`-module which is, as an abelian group, isomorphic
to `(ℤ/ℓⁿ)^r`. Then the underlying abelian sheaf of `F` is pro-étale locally isomorphic to
`(ℤ/ℓⁿ)_X^r`, in the form of the hypothesis `hloc` of
`ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit`
(`AlgebraicGeometry.ProEtale.exists_sieve_nonempty_isoPresheaf_zmodPowAbSheafDiagramPow`).

The ingredients are:

* the slice `X_proét / W` of the small pro-étale site over `W : X_proét` maps to `W_proét`
  (`AlgebraicGeometry.Scheme.ProEt.overToLocalization`), compatibly with the localization functor,
  so that isomorphisms of the restrictions along the localization functor give isomorphisms of the
  restrictions to the slice
  (`AlgebraicGeometry.ProEtale.overPullbackIsoOfLocalizationRestrictionIso`);
* local isomorphisms over the members of a pro-étale cover of `X` give local isomorphisms over any
  object, by base change (`AlgebraicGeometry.ProEtale.exists_sieve_nonempty_isoPresheaf_of_cover`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} (W : X.ProEt)

/-- An object `T ⟶ W` of the slice `X_proét / W` is weakly étale over `W`. -/
lemma weaklyEtale_hom_left (T : Over W) : WeaklyEtale T.hom.left :=
  MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) T.hom.left W.hom W.prop
    ((MorphismProperty.Over.w T.hom).symm ▸ T.left.prop)

/-- The functor from the slice `X_proét / W` to `W_proét`, sending `T ⟶ W` to `T` viewed as a
weakly étale `W`-scheme. -/
noncomputable def overToLocalization : Over W ⥤ W.left.ProEt where
  obj T := MorphismProperty.Over.mk ⊤ T.hom.left (weaklyEtale_hom_left W T)
  map {T T'} φ := MorphismProperty.Over.homMk φ.left.left (by
    exact (MorphismProperty.Comma.comp_left _ _).symm.trans
      (congr_arg (fun ψ : T.left ⟶ W ↦ ψ.left) (Over.w φ)))

/-- The component at `T` of `ProEt.overToLocalizationCompOverMapIso`. -/
noncomputable def overToLocalizationCompOverMapIsoApp (T : Over W) :
    (MorphismProperty.Over.map ⊤ W.prop).obj ((overToLocalization W).obj T) ≅ T.left :=
  MorphismProperty.Over.isoMk (Iso.refl _)
    ((Category.id_comp _).trans (MorphismProperty.Over.w T.hom).symm)

/-- The functor `ProEt.overToLocalization W` followed by the localization functor
`W_proét ⥤ X_proét` is the forgetful functor of the slice. -/
noncomputable def overToLocalizationCompOverMapIso :
    overToLocalization W ⋙ MorphismProperty.Over.map ⊤ W.prop ≅ Over.forget W :=
  NatIso.ofComponents (overToLocalizationCompOverMapIsoApp W) (fun φ ↦ by
      ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Abelian.hasFiniteBiproducts

variable {X : Scheme.{u}}

/-- **Isomorphisms after localization are isomorphisms over the slice**: an isomorphism of the
restrictions of two sheaves along the localization functor `W_proét ⥤ X_proét` gives an
isomorphism of their restrictions to the slice `X_proét / W`. -/
noncomputable def overPullbackIsoOfLocalizationRestrictionIso {A : Type*} [Category.{u + 1} A]
    {W : X.ProEt} {F G : Sheaf (ProEt.topology X) A}
    (e : (ProEtale.localizationRestriction A W.hom W.prop).obj F ≅
      (ProEtale.localizationRestriction A W.hom W.prop).obj G) :
    ((ProEt.topology X).overPullback A W).obj F ≅
      ((ProEt.topology X).overPullback A W).obj G :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight (NatIso.op (ProEt.overToLocalizationCompOverMapIso W)) F.obj ≪≫
      Functor.isoWhiskerLeft (ProEt.overToLocalization W).op ((sheafToPresheaf _ _).mapIso e) ≪≫
      (Functor.isoWhiskerRight (NatIso.op (ProEt.overToLocalizationCompOverMapIso W)) G.obj).symm)

/-- The projection `V ×_X W ⟶ W`, as a morphism of the small pro-étale site of `X`. -/
noncomputable def baseChangeToMk {W : Scheme.{u}} (g : W ⟶ X) [WeaklyEtale g] (V : X.ProEt) :
    ProEt.baseChange g V ⟶ ProEt.mk g :=
  MorphismProperty.Over.homMk (pullback.snd V.hom g) pullback.condition.symm

/-- **Local isomorphisms over a cover of `X` are local over every object**: if two pro-étale
sheaves are isomorphic over the members of a pro-étale cover `gᵢ : Wᵢ ⟶ X`, then over every
`V : X_proét` they are isomorphic on a covering sieve (formed by the base changes `V ×_X Wᵢ`). -/
theorem exists_sieve_nonempty_isoPresheaf_of_cover {A : Type*} [Category.{u + 1} A]
    {F G : Sheaf (ProEt.topology X) A} {κ : Type*} {W : κ → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    [∀ i, WeaklyEtale (g i)] (hg : Presieve.ofArrows W g ∈ proetalePrecoverage X)
    (e : ∀ i, (isoPresheaf F G).obj (op (ProEt.mk (g i)))) (V : X.ProEt) :
    ∃ S ∈ ProEt.topology X V, ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), S f →
      Nonempty ((isoPresheaf F G).obj (op Y)) := by
  refine ⟨_, ProEt.ofArrows_baseChange_mem_topology V g hg, fun Y f hf ↦ ?_⟩
  obtain ⟨_, h, _, ⟨i⟩, rfl⟩ := hf
  exact ⟨(isoPresheaf F G).map (h ≫ baseChangeToMk (g i) V).op (e i)⟩

section ConstantSheaf

variable {Λ : Type (u + 1)} [CommRing Λ] (W : Scheme.{u})

/-- **The underlying abelian sheaf of a constant sheaf of modules is constant**: on the small
pro-étale site, the abelian sheaf underlying the constant sheaf of `Λ`-modules with value `M` is
the constant sheaf with value the abelian group underlying `M`. Both functors
`M ↦ (M_W)^{ab}` and `M ↦ (M^{ab})_W` are left adjoint to `P ↦ R(P(W))`, where `R` is right
adjoint to the forgetful functor from `Λ`-modules to abelian groups. -/
noncomputable def sheafComposeForget₂ConstantSheafIso :
    constantSheaf (ProEt.topology W) (ModuleCat.{u + 1} Λ) ⋙
        sheafCompose (ProEt.topology W) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}) ≅
      forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1} ⋙ constantSheaf (ProEt.topology W) Ab.{u + 1} :=
  let adjF := Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})
  have : PreservesLimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}).rightAdjoint :=
    adjF.rightAdjoint_preservesLimits
  have : (ProEt.topology W).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}).rightAdjoint :=
    hasSheafCompose_of_preservesLimitsOfSize _
  let adjS := (Sheaf.adjunction (ProEt.topology W) adjF).ofNatIsoLeft
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso _ _)
  ((adjF.comp (constantSheafAdj (ProEt.topology W) Ab.{u + 1}
    (ProEt.isTerminalMkId W))).ofNatIsoRight (Iso.refl _)).leftAdjointUniq
    ((constantSheafAdj (ProEt.topology W) (ModuleCat.{u + 1} Λ) (ProEt.isTerminalMkId W)).comp
      adjS) |>.symm

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts in
/-- The constant sheaf functor on abelian groups is additive, being a left adjoint. -/
instance additive_constantSheaf : (constantSheaf (ProEt.topology W) Ab.{u + 1}).Additive :=
  have := (constantSheafAdj (ProEt.topology W) Ab.{u + 1} (ProEt.isTerminalMkId W)).isLeftAdjoint
  Functor.additive_of_preservesBinaryBiproducts _

variable (l : ℕ)

/-- The constant abelian sheaf `ℤ/N` on `W_proét` is the sheaf `(ℤ/N)_W` of locally constant
functions. -/
noncomputable def constantSheafZModIso (N : ℕ) :
    (constantSheaf (ProEt.topology W) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))) ≅
      (sheafCompose (ProEt.topology W) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf W (ZMod N)) :=
  (presheafToSheaf (ProEt.topology W) Ab.{u + 1}).mapIso
    (Functor.constComp _ (RingCat.of (ULift.{u + 1} (ZMod N))) (forget₂ RingCat Ab)).symm ≪≫
    zmodConstSheafRingIso W N

/-- The constant abelian sheaf with value an abelian group isomorphic to `(ℤ/ℓⁿ)^r` is
`(ℤ/ℓⁿ)_W^r`. -/
noncomputable def constantSheafIsoZModPowAbSheafDiagramPow {M : Ab.{u + 1}} {r n : ℕ}
    (eM : M ≃+ (Fin r → ZMod (l ^ n))) :
    (constantSheaf (ProEt.topology W) Ab.{u + 1}).obj M ≅
      (zmodPowAbSheafDiagramPow W l r).obj (op n) :=
  (constantSheaf (ProEt.topology W) Ab.{u + 1}).mapIso
      ((eM.trans (AddEquiv.piCongrRight fun _ ↦ AddEquiv.ulift.symm)).toAddCommGrpIso ≪≫
        (AddCommGrpCat.biproductIsoPi fun _ : Fin r ↦
          AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ n)))).symm) ≪≫
    (constantSheaf (ProEt.topology W) Ab.{u + 1}).mapBiproduct _ ≪≫
    biproduct.mapIso fun _ ↦ constantSheafZModIso W (l ^ n)

end ConstantSheaf

section Local

variable {Λ : Type (u + 1)} [CommRing Λ] (l : ℕ)

/-- Restriction along the localization functor of a weakly étale morphism is additive. -/
instance additive_localizationRestriction {W : Scheme.{u}} (g : W ⟶ X) (h : WeaklyEtale g) :
    (ProEtale.localizationRestriction Ab.{u + 1} g h).Additive where
  map_add := by
    intros
    rfl

/-- The restriction of `(ℤ/ℓⁿ)_X^r` along the localization functor of a weakly étale
`g : W ⟶ X` is `(ℤ/ℓⁿ)_W^r`: the sections of both over `T` are the locally constant functions
on `T`. -/
noncomputable def localizationRestrictionZModPowAbSheafDiagramPowIso {W : Scheme.{u}}
    (g : W ⟶ X) (h : WeaklyEtale g) (r n : ℕ) :
    (ProEtale.localizationRestriction Ab.{u + 1} g h).obj
        ((zmodPowAbSheafDiagramPow X l r).obj (op n)) ≅
      (zmodPowAbSheafDiagramPow W l r).obj (op n) :=
  (ProEtale.localizationRestriction Ab.{u + 1} g h).mapBiproduct _ ≪≫
    biproduct.mapIso fun _ ↦ Iso.refl _

/-- **Local triviality after localization**: if the pullback `g^* F` of a pro-étale sheaf of
`Λ`-modules along a weakly étale `g : W ⟶ X` is the constant sheaf of a `Λ`-module which is
isomorphic to `(ℤ/ℓⁿ)^r` as an abelian group, then the restriction of the underlying abelian
sheaf of `F` along the localization functor is isomorphic to that of `(ℤ/ℓⁿ)_X^r`. -/
noncomputable def localizationRestrictionIsoOfUpperStarIso {W : Scheme.{u}} (g : W ⟶ X)
    (h : WeaklyEtale g) (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (M : ModuleCat.{u + 1} Λ) {r n : ℕ} (eM : M ≃+ (Fin r → ZMod (l ^ n)))
    (e : (g)^*[ModuleCat.{u + 1} Λ].obj F ≅
      (constantSheaf (ProEt.topology W) (ModuleCat.{u + 1} Λ)).obj M) :
    (ProEtale.localizationRestriction Ab.{u + 1} g h).obj
        ((zmodPowAbSheafDiagramPow X l r).obj (op n)) ≅
      (ProEtale.localizationRestriction Ab.{u + 1} g h).obj
        ((sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).obj F) :=
  localizationRestrictionZModPowAbSheafDiagramPowIso l g h r n ≪≫
    (constantSheafIsoZModPowAbSheafDiagramPow W l
      (M := (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1}).obj M) eM).symm ≪≫
    ((sheafComposeForget₂ConstantSheafIso W).app M).symm ≪≫
    (sheafCompose (ProEt.topology W) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).mapIso
      (e.symm ≪≫ (ProEtale.upperStarIsoLocalizationRestriction _ g h).app F)

/-- **Pro-étale sheaves which are locally constant with free stalks over `ℤ/ℓⁿ` are locally
`(ℤ/ℓⁿ)_X^r`**: let `F` be a pro-étale sheaf of `Λ`-modules and `gᵢ : Wᵢ ⟶ X` a pro-étale
cover such that each `gᵢ^* F` is the constant sheaf of a `Λ`-module isomorphic to `(ℤ/ℓⁿ)^r` as an
abelian group. Then the underlying abelian sheaf of `F` is locally isomorphic to `(ℤ/ℓⁿ)_X^r`
over every object, in the form of the hypothesis `hloc` of
`ProEtale.isAdicLisseSheaf_adicSheafExtendScalars_limit`. -/
theorem exists_sieve_nonempty_isoPresheaf_zmodPowAbSheafDiagramPow
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (r n : ℕ) {κ : Type*}
    {W : κ → Scheme.{u}} (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows W g ∈ proetalePrecoverage X) (M : κ → ModuleCat.{u + 1} Λ)
    (eM : ∀ i, M i ≃+ (Fin r → ZMod (l ^ n)))
    (e : ∀ i, (g i)^*[ModuleCat.{u + 1} Λ].obj F ≅
      (constantSheaf (ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj (M i))
    (V : X.ProEt) :
    ∃ S ∈ ProEt.topology X V, ∀ ⦃Y : X.ProEt⦄ (f : Y ⟶ V), S f →
      Nonempty ((isoPresheaf ((zmodPowAbSheafDiagramPow X l r).obj (op n))
        ((sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) Ab.{u + 1})).obj F)).obj
          (op Y)) :=
  exists_sieve_nonempty_isoPresheaf_of_cover g hg (fun i ↦
    overPullbackIsoOfLocalizationRestrictionIso (W := ProEt.mk (g i))
      (localizationRestrictionIsoOfUpperStarIso l (g i) inferInstance F (M i) (eM i) (e i))) V

/-- **`ν^*` of an étale sheaf which is étale locally constant with value `(ℤ/ℓⁿ)^r` is pro-étale
locally `(ℤ/ℓⁿ)_X^r`**: let `G` be an étale sheaf of `Λ`-modules and `fᵢ : Uᵢ ⟶ X` an étale
cover such that each `fᵢ^* G` is the constant sheaf of a `Λ`-module isomorphic to `(ℤ/ℓⁿ)^r` as
an abelian group. Then the abelian sheaf underlying `ν^* G` is locally isomorphic to
`(ℤ/ℓⁿ)_X^r` over every object of `X_proét`: `ν^*` commutes with the pullbacks along the `fᵢ`
and sends constant sheaves to constant sheaves. -/
theorem exists_sieve_nonempty_isoPresheaf_zmodPowAbSheafDiagramPow_comparisonUpperStarAb
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (r n : ℕ) {κ : Type*}
    {U : κ → Scheme.{u}} (f : ∀ i, U i ⟶ X) (hf : Presieve.ofArrows U f ∈ etalePrecoverage X)
    (M : κ → ModuleCat.{u + 1} Λ) (eM : ∀ i, M i ≃+ (Fin r → ZMod (l ^ n)))
    (e : ∀ i, (Etale.upperStar (ModuleCat.{u + 1} Λ) (f i)).obj G ≅
      (constantSheaf (U i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))
    (V : X.ProEt) :
    ∃ S ∈ ProEt.topology X V, ∀ ⦃Y : X.ProEt⦄ (g : Y ⟶ V), S g →
      Nonempty ((isoPresheaf ((zmodPowAbSheafDiagramPow X l r).obj (op n))
        ((comparisonUpperStarAb Λ X).obj G)).obj (op Y)) :=
  have (i : κ) : Etale (f i) := ((Scheme.ofArrows_mem_precoverage_iff _).1 hf).2 i
  exists_sieve_nonempty_isoPresheaf_zmodPowAbSheafDiagramPow l
    ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj G) r n f (etalePrecoverage_le_proetalePrecoverage _ hf) M
    eM (fun i ↦ (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) (f i)).app G ≪≫
      (ν^*(U i)[ModuleCat.{u + 1} Λ]).mapIso (e i) ≪≫
      (comparisonUpperStarConstantSheafIso Λ (U i)).app (M i)) V

variable (X) in
/-- **Étale `ℓ`-adic towers of rank `r` give lisse `ℓ`-adic sheaves.** Let `(Gₙ)` be a tower of
étale sheaves of `Λ`-modules on `X` with `ℓⁿ Gₙ = 0`, whose transitions are cokernels of `ℓⁿ`,
and such that each `Gₙ` is étale locally constant with value an abelian group isomorphic to
`(ℤ/ℓⁿ)^r`. Then `ℚ̄_ℓ ⊗ lim ν^* Gₙ`, the limit being taken in `ℤ_ℓ,X`-modules, is lisse. -/
theorem isAdicLisseSheaf_adicSheafExtendScalars_limit_comparisonPadicIntModTower [Fact l.Prime]
    (r : ℕ) (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∀ n : ℕ, ((l ^ n : ℕ) : ℤ) • 𝟙 (G.obj (op n)) = 0)
    (hcok : ∀ n : ℕ, ∃ w : (((l ^ n : ℕ) : ℤ) • 𝟙 _) ≫ G.map (homOfLE n.le_succ).op = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)))
    (htriv : ∀ n : ℕ, ∃ (κ : Type u) (U : κ → Scheme.{u}) (f : ∀ i, U i ⟶ X),
      Presieve.ofArrows U f ∈ etalePrecoverage X ∧ ∀ i, ∃ M : ModuleCat.{u + 1} Λ,
        Nonempty (M ≃+ (Fin r → ZMod (l ^ n))) ∧
        Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (f i)).obj (G.obj (op n)) ≅
          (constantSheaf (U i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    IsAdicLisseSheaf ((adicSheafExtendScalars X l).obj
      (limit (comparisonPadicIntModTower X l G hG))) :=
  isAdicLisseSheaf_adicSheafExtendScalars_limit X l r _
    (exists_isColimit_comparisonPadicIntModTower X l G hG hcok) fun n V ↦ by
      obtain ⟨κ, U, f, hf, h⟩ := htriv n
      choose M hM e using h
      exact exists_sieve_nonempty_isoPresheaf_zmodPowAbSheafDiagramPow_comparisonUpperStarAb l
        (G.obj (op n)) r n f hf M (fun i ↦ (hM i).some) (fun i ↦ (e i).some) V

end Local

end AlgebraicGeometry.ProEtale
