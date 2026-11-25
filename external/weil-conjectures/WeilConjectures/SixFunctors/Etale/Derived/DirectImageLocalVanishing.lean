/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension

/-!
# Local criteria for the vanishing of higher direct images

Let `f : X ⟶ Y` be a morphism of schemes and `M` an étale sheaf of `Λ`-modules on `X`. The higher
direct image `R^q f_* M` is the sheafification of the presheaf `W ↦ H^q(W ×_Y X, M|)` on `Y_ét`.
This file records two criteria for its vanishing.

* `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_exists`: for a torsion ring `Λ`,
  `R^q f_* M = 0` for `q > c` as soon as every étale `Y`-scheme `W` is covered by étale
  `Y`-schemes `V ⟶ W` with `V ×_Y X` of torsion cohomological dimension at most `c`. This is
  `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_isAffine` with a local hypothesis:
  only a neighbourhood of every point of every `W` has to be controlled.
* `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_isSepClosed`: for a morphism of
  finite-type schemes over a field `K`, `R^q f_* M = 0` as soon as the same holds after every base
  change to a separably closed field. This is the limit argument of
  `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_topologicalKrullDim_le`, with its
  separably closed input made a hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Higher direct images vanish when the cohomology vanishes locally.** For `h : Y ⟶ X` and an
étale sheaf `F` of `Λ`-modules on `Y`, `R^q h_* F = 0` as soon as every point of every étale
`X`-scheme `W` lies in the image of an étale `X`-scheme `V ⟶ W` with `H^q(V ×_X Y, F|) = 0`.
A section of `R^q h_* F` is locally a class of the presheaf `V ↦ H^q(V ×_X Y, F|)`
(`AlgebraicGeometry.Etale.isLocallyBijective_higherDirectImagePresheafToSheaf`), hence locally
zero. -/
theorem Etale.isZero_higherDirectImage_of_forall_exists_subsingleton {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : ∀ (W : X.Etale) (x : W.left), ∃ (V : X.Etale) (g : V ⟶ W), x ∈ Set.range g.left ∧
      Subsingleton ((Etale.higherDirectImagePresheaf Λ h q
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).obj (op V))) :
    IsZero (Etale.higherDirectImage Λ h q F) := by
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let G := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj (Etale.higherDirectImage Λ h q F)
  let GT := (sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G
  let φ := Etale.higherDirectImagePresheafToSheaf Λ h q K
  obtain ⟨-, hφ⟩ := Etale.isLocallyBijective_higherDirectImagePresheafToSheaf Λ h q K
  have h₂ (U : X.Etale) (s : G.obj.obj (op U)) : s = 0 := by
    let S : Sieve U :=
      { arrows := fun V f ↦ G.obj.map f.op s = 0
        downward_closed := fun {V W} f hf g ↦ by
          rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hf, map_zero] }
    have hS : S ∈ X.smallEtaleTopology U := by
      rw [Scheme.mem_smallEtaleTopology_iff]
      intro x
      obtain ⟨V₁, g₁, ⟨t, ht⟩, x₁, rfl⟩ :=
        (Scheme.mem_smallEtaleTopology_iff _).1 (hφ.imageSieve_mem s) x
      obtain ⟨V₂, g₂, ⟨x₂, rfl⟩, hsub⟩ := H V₁ x₁
      refine ⟨V₂, g₂ ≫ g₁, ?_, ⟨x₂, rfl⟩⟩
      change G.obj.map (g₂ ≫ g₁).op s = 0
      have hn := ConcreteCategory.congr_hom (φ.naturality g₂.op) t
      simp only [ConcreteCategory.comp_apply] at hn
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      erw [← ht, ← hn, Subsingleton.elim ((Etale.higherDirectImagePresheaf Λ h q K).map g₂.op t) 0,
        map_zero]
    exact ((isSheaf_iff_isSheaf_of_type _ _).1 GT.property _ hS).isSeparatedFor.ext
      fun V f hf ↦ by
        change G.obj.map f.op s = G.obj.map f.op 0
        rw [map_zero]
        exact hf
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact h₂ U.unop x

/-- The local criterion
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_exists_subsingleton`
in terms of cohomological dimension, for a coefficient ring whose injective sheaves have acyclic
underlying abelian sheaves and a sheaf `M` whose restrictions are torsion: `R^q f_* M = 0` for
`q > c` as soon as every point of every étale `Y`-scheme `W` lies in the image of an étale
`Y`-scheme `V ⟶ W` such that `V ×_Y X` has torsion cohomological dimension at most `c`. -/
theorem Etale.isZero_higherDirectImage_of_forall_exists_of_acyclic {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (hI : ∀ (V : X.Etale) (I : Sheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [Injective I] (m : ℕ), Subsingleton (Sheaf.H ((sheafCompose V.left.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj I) (m + 1)))
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hM : ∀ V : X.Etale, ((sheafCompose V.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((V.hom)^*[ModuleCat.{u + 1} Λ].obj M)).IsTorsion)
    (c : ℕ) (H : ∀ (W : Y.Etale) (y : W.left), ∃ (V : Y.Etale) (g : V ⟶ W),
      y ∈ Set.range g.left ∧
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left.HasTorsionCohomologicalDimensionLE
          c)
    (q : ℤ) (hq : (c : ℤ) < q) :
    IsZero (Etale.higherDirectImage Λ f q M) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = ((n + 1 : ℕ) : ℤ) := ⟨(q - 1).toNat, by omega⟩
  refine Etale.isZero_higherDirectImage_of_forall_exists_subsingleton f _ M fun W y ↦ ?_
  obtain ⟨V, g, hy, hV⟩ := H W y
  refine ⟨V, g, hy, ?_⟩
  let V' := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V
  have hcd : Subsingleton (Sheaf.H ((sheafCompose V'.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((V'.hom)^*[ModuleCat.{u + 1} Λ].obj M)) (n + 1)) :=
    hV _ (hM V') (n + 1) (by omega)
  have : Subsingleton (Abelian.Ext.{u + 1} ((Etale.freeSheaf Λ X).obj V') M (n + 1)) :=
    Etale.subsingleton_ext_freeSheaf_of_subsingleton_H_of_acyclic V' M n (hI V') hcd
  exact ((DerivedCategory.Plus.singleFunctorHomEquivExt.{u + 1}
    ((f)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ Y).obj V)) M (n + 1)).trans
    (Abelian.Ext.precompAddEquiv (Etale.upperStarFreeSheafIso Λ f V) M (n + 1)).symm.toEquiv
    ).subsingleton

/-- **Vanishing of higher direct images from local cohomological dimension bounds.** Let `Λ` be a
ring which is torsion as an additive group, `f : X ⟶ Y` a morphism of schemes and `c ∈ ℕ`. If
every point of every étale `Y`-scheme `W` lies in the image of an étale `Y`-scheme `V ⟶ W` such
that `V ×_Y X` has torsion cohomological dimension at most `c`, then `R^q f_* M = 0` for every
étale sheaf `M` of `Λ`-modules on `X` and every `q > c`.

By restriction of scalars to `ULift ℤ`, as in
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_quasiCompact_of_two_mul_lt`, this is
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_exists_of_acyclic`. -/
theorem Etale.isZero_higherDirectImage_of_forall_exists (hΛ : IsAddTorsion Λ)
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (c : ℕ) (H : ∀ (W : Y.Etale) (y : W.left), ∃ (V : Y.Etale) (g : V ⟶ W),
      y ∈ Set.range g.left ∧
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left.HasTorsionCohomologicalDimensionLE
          c)
    (q : ℤ) (hq : (c : ℤ) < q) :
    IsZero (Etale.higherDirectImage Λ f q M) := by
  let φ := Etale.uliftIntRingHom Λ
  obtain ⟨m, hm, hm1⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hΛ (1 : Λ))
  have hz := Etale.isZero_higherDirectImage_of_forall_exists_of_acyclic f
    (fun V I _ n ↦ Etale.subsingleton_H_forget₂_uliftInt_of_injective I n)
    ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) (fun V ↦ ?_) c H q hq
  · have hz' := IsZero.of_iso hz (Etale.restrictScalarsHigherDirectImageIso f q M)
    rw [IsZero.iff_id_eq_zero] at hz' ⊢
    refine (Sheaf.restrictScalars Y.smallEtaleTopology φ).map_injective ?_
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    exact hz'
  · refine Sheaf.IsTorsion.of_iso ((sheafCompose V.left.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).mapIso
        (asIso ((Etale.upperStarRestrictScalars φ V.hom).app M)).symm) ?_
    refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U x ↦ ?_
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm, ?_⟩
    let y : ((V.hom)^*[ModuleCat.{u + 1} Λ].obj M).obj.obj U := x
    change m • y = 0
    rw [← one_smul Λ y, ← smul_assoc, hm1, zero_smul]

variable (Λ) in
/-- **Reduction of the vanishing of higher direct images to separably closed fields.** Let `K` be
a field and `f : X ⟶ Y` a morphism of `K`-schemes of finite type. If for every separably closed
field `L` over `K`, with base change `p₁ : X_L ⟶ X`, the higher direct image
`R^q (p₁ ≫ f)_* (p₁^* F)` vanishes, then so does `R^q f_* F`.

This is the limit argument of
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_topologicalKrullDim_le`: by the limit
theorem `AlgebraicGeometry.Etale.higherDirectImage_limit` the stalks of `R^q (X_L → Y)_* F` over
the finite subextensions `L` of `K^sep / K` have colimit the stalk of `R^q (X_{K^sep} → Y)_* F`,
which vanishes by hypothesis, and the transition maps from `R^q f_* F` are monomorphisms
(`AlgebraicGeometry.Etale.mono_higherDirectImageOverMap`). -/
theorem Etale.isZero_higherDirectImage_of_forall_isSepClosed {K : Type u} [Field K]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℤ)
    (H : ∀ (L : Type u) [Field L] [IsSepClosed L] (s : Spec (.of L) ⟶ Spec (.of K))
      {P : Scheme.{u}} (p₁ : P ⟶ X) (p₂ : P ⟶ Spec (.of L)), IsPullback p₁ p₂ aX s →
        IsZero (Etale.higherDirectImage Λ (p₁ ≫ f) q ((p₁)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsZero (Etale.higherDirectImage Λ f q F) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := ⟨⟩
  -- the cofiltered system of the `X_L`, for the finite subextensions `L` of `K^sep / K`
  let Ks := SeparableClosure K
  let I := IntermediateField.FiniteSubext K Ks
  let D : Iᵒᵖ ⥤ Scheme.{u} := (IntermediateField.subextDiagram K Ks).op ⋙ Scheme.Spec
  let c : Cone D := subextSpecCone K Ks
  have hc : IsLimit c := isLimitSubextSpecCone K Ks
  have hD {i j : Iᵒᵖ} (g : i ⟶ j) : IsAffineHom (D.map g) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  let i₀ : Iᵒᵖ := Opposite.op ⟨⊥, inferInstance⟩
  let ρ : CommRingCat.of (⊥ : IntermediateField K Ks) ≅ CommRingCat.of K :=
    (IntermediateField.botEquiv K Ks).toRingEquiv.toCommRingCatIso
  let p : X ⟶ D.obj i₀ := aX ≫ Spec.map ρ.hom
  let pY : Y ⟶ D.obj i₀ := aY ≫ Spec.map ρ.hom
  let D' := baseChangeDiagram D p
  let c' := baseChangeCone D c p
  have hc' : IsLimit c' := isLimitBaseChangeCone D c p hc
  let D'' : Over i₀ ⥤ Over X :=
    { obj j := Over.mk (pullback.fst p (D.map j.hom))
      map g := Over.homMk (D'.map g) (baseChangeDiagram_map_fst D p g)
      map_id j := by ext1; exact D'.map_id j
      map_comp g h := by ext1; exact D'.map_comp g h }
  let c'' : Cone D'' :=
    { pt := Over.mk (pullback.fst p (c.π.app i₀))
      π := { app j := Over.homMk (c'.π.app j) (baseChangeCone_π_app_fst D c p j)
             naturality j j' g := by ext1; exact c'.π.naturality g } }
  have hc'' : IsLimit ((Over.forget X).mapCone c'') := hc'
  have : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := hD
  have (j j' : Over i₀) (g : j ⟶ j') : IsAffineHom (D''.map g).left :=
    inferInstanceAs (IsAffineHom (D'.map g))
  have (j : Over i₀) : QuasiCompact ((D''.obj j).hom ≫ f) :=
    inferInstanceAs (QuasiCompact (pullback.fst p (D.map j.hom) ≫ f))
  have (j : Over i₀) : QuasiSeparated ((D''.obj j).hom ≫ f) := by
    have : IsAffine (D.obj j.left) := inferInstanceAs (IsAffine (Spec _))
    have : QuasiSeparatedSpace (D''.obj j).left :=
      (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p (D.map j.hom))).mp inferInstance
    exact inferInstanceAs (QuasiSeparated (pullback.fst p (D.map j.hom) ≫ f))
  have : IsAffine c.pt := inferInstanceAs (IsAffine (Spec _))
  have : IsAffineHom (c.π.app i₀) := inferInstanceAs (IsAffineHom (Spec.map _))
  have : QuasiCompact (c''.pt.hom ≫ f) :=
    inferInstanceAs (QuasiCompact (pullback.fst p (c.π.app i₀) ≫ f))
  have : QuasiSeparated (c''.pt.hom ≫ f) := by
    have : QuasiSeparatedSpace c''.pt.left :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (c.π.app i₀))
    exact inferInstanceAs (QuasiSeparated (pullback.fst p (c.π.app i₀) ≫ f))
  -- the higher direct image vanishes over the limit `X_{K^sep}`
  have hT : IsZero (Etale.higherDirectImage Λ (c''.pt.hom ≫ f) q
      ((c''.pt.hom)^*[ModuleCat.{u + 1} Λ].obj F)) := by
    let aT : pullback p (c.π.app i₀) ⟶ Spec (.of Ks) := pullback.snd p (c.π.app i₀)
    have hρ : (Scheme.Spec.mapIso ρ.symm.op).hom = Spec.map ρ.inv := rfl
    have hρρ : Spec.map ρ.hom ≫ Spec.map ρ.inv = 𝟙 _ := by
      rw [← Spec.map_comp, ρ.inv_hom_id, Spec.map_id]
    have hpb : IsPullback (pullback.fst p (c.π.app i₀)) aT aX
        (c.π.app i₀ ≫ Spec.map ρ.inv) :=
      (IsPullback.of_hasPullback p (c.π.app i₀)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (Scheme.Spec.mapIso ρ.symm.op) (by simp)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        (by
          erw [hρ]
          exact (Category.assoc _ _ _).trans ((congrArg (aX ≫ ·) hρρ).trans
            (Category.comp_id _)))
        (by
          erw [hρ]
          exact (Category.id_comp _).symm)
    exact H Ks _ (pullback.fst p (c.π.app i₀)) aT hpb
  -- the transition maps from `X` to the stages `X_L` are monomorphisms
  let X₀ : Over X := Over.mk (𝟙 X)
  have hmono (j : Over i₀) (ψ : D''.obj j ⟶ X₀) :
      Mono (Etale.higherDirectImageOverMap Λ f F q ψ) := by
    let L : IntermediateField K Ks := j.left.unop.1
    have : FiniteDimensional K L := j.left.unop.2
    have hr : (IntermediateField.subextDiagram K Ks).map j.hom.unop =
        ρ.hom ≫ CommRingCat.ofHom (algebraMap K L) := by
      ext x
      exact IntermediateField.inclusion_bot_apply _ _ x
    have hDj : D.map j.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Spec.map ρ.hom := by
      rw [← Spec.map_comp, ← hr]
      rfl
    have : IsIso (Spec.map ρ.hom) := inferInstanceAs (IsIso (Scheme.Spec.mapIso ρ.op).hom)
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
      have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
      have : Algebra.FinitePresentation K L :=
        Algebra.FinitePresentation.of_finiteType.mp inferInstance
      exact HasRingHomProperty.Spec_iff.mpr
        (RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩)
    have hE : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Spec.map ρ.hom) :=
      inferInstance
    have hS : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ Spec.map ρ.hom) :=
      inferInstance
    have : Etale (D.map j.hom) := by
      rw [hDj]
      exact hE
    have : Surjective (D.map j.hom) := by
      rw [hDj]
      exact hS
    have hψ : ψ.left = pullback.fst p (D.map j.hom) := by simpa [X₀, D''] using Over.w ψ
    have h₂ := pullback.condition (f := pY) (g := D.map j.hom)
    refine Etale.mono_higherDirectImageOverMap Λ f F q ψ (pullback.fst pY (D.map j.hom))
      (Surjective.surj (f := pullback.fst pY (D.map j.hom)))
      (IsPullback.of_hasPullback (X₀.hom ≫ f) (pullback.fst pY (D.map j.hom)))
      (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd pY (D.map j.hom)) ?_) ?_
    · have h₃ : (X₀.hom ≫ f) ≫ pY = p := by simp [X₀, p, pY, ← hf]
      rw [← h₃]
      exact (pullback.condition_assoc pY).trans ((congrArg (_ ≫ ·) h₂).trans
        (Category.assoc _ _ _).symm)
    · rw [hψ, pullback.lift_fst]
  -- hence the higher direct image vanishes, by the limit theorem
  let R₀ := Etale.higherDirectImage Λ (X₀.hom ≫ f) q ((X₀.hom)^*[ModuleCat.{u + 1} Λ].obj F)
  have hR₀ : IsZero R₀ := Etale.isZero_higherDirectImage_of_isLimit_of_mono Λ f F D'' c'' hc'' q
    (i₀ := Over.mk (𝟙 i₀)) (Over.homMk (D''.obj (Over.mk (𝟙 i₀))).hom (by simp [X₀])) hmono hT
  have e : R₀ = Etale.higherDirectImage Λ f q ((𝟙 X)^*[ModuleCat.{u + 1} Λ].obj F) := by
    simp [R₀, X₀]
  rw [e] at hR₀
  exact hR₀.of_iso ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (R+((f)_*[ModuleCat.{u + 1} Λ]).mapIso ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((Etale.upperStarId (ModuleCat.{u + 1} Λ) X).app F).symm)))

end AlgebraicGeometry
