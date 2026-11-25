/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map

/-!
# Functoriality and exactness of the geometric stalks of Weil sheaves

The geometric stalk `F_s = Γ(Spec k̄, s^* F)` of a Weil sheaf at a geometric point `s` is
functorial in `F`: it is the functor `AlgebraicGeometry.WeilSheaf.stalkFunctor`, the composite of
the forgetful functor to pro-étale sheaves on `X̄`, the pullback `s^*` and the global sections
on `Spec k̄`. It is exact: the forgetful functor and `s^*` are exact, and the global sections on
the spectrum of an algebraically closed field are exact
(`AlgebraicGeometry.ProEtale.preservesEpimorphisms_Γ_of_isAlgClosed`). The map induced on the
stalks by a morphism of Weil sheaves commutes with the Frobenius of the stalks, since the Weil
structures commute with it.

As a consequence, punctual purity passes to subobjects and quotients: the stalks of a subobject
(resp. a quotient) are Frobenius-stable subspaces (resp. quotients) of the stalks.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.stalkFunctor`: the stalk functor at a geometric point.
- `AlgebraicGeometry.WeilSheaf.stalkMap`: the map induced on the stalks by a morphism.
- `AlgebraicGeometry.WeilSheaf.stalkAt_frobenius_map`: the induced map commutes with the
  Frobenius.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.of_mono` and
  `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.of_epi`: punctual purity of subobjects
  and quotients.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

section Functor

variable (k₀ l X) in
/-- The underlying pro-étale sheaf of `ℚ̄_ℓ`-modules on `X̄` of a Weil sheaf, as a functor. -/
noncomputable abbrev sheafFunctor : WeilSheaf k₀ l X ⥤
    Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l) :=
  ObjectProperty.ι _ ⋙ IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _

instance preservesMonomorphisms_ι_objectProperty :
    (WeilSheaf.objectProperty k₀ l X).ι.PreservesMonomorphisms :=
  ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory _

instance preservesEpimorphisms_ι_objectProperty :
    (WeilSheaf.objectProperty k₀ l X).ι.PreservesEpimorphisms :=
  ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory _

instance preservesMonomorphisms_forget_frobeniusPullback :
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).PreservesMonomorphisms :=
  inferInstance

instance preservesEpimorphisms_forget_frobeniusPullback :
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).PreservesEpimorphisms :=
  inferInstance

instance preservesMonomorphisms_adicSheafForget :
    (ProEtale.AdicSheaf.forget (l := l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).PreservesMonomorphisms :=
  inferInstance

instance preservesEpimorphisms_adicSheafForget :
    (ProEtale.AdicSheaf.forget (l := l)
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).PreservesEpimorphisms :=
  inferInstance

instance preservesMonomorphisms_sheafFunctor : (sheafFunctor k₀ l X).PreservesMonomorphisms :=
  @Functor.preservesMonomorphisms_comp _ _ _ _ _ _ _ _ preservesMonomorphisms_ι_objectProperty
    (@Functor.preservesMonomorphisms_comp _ _ _ _ _ _ _ _
      preservesMonomorphisms_forget_frobeniusPullback preservesMonomorphisms_adicSheafForget)

instance preservesEpimorphisms_sheafFunctor : (sheafFunctor k₀ l X).PreservesEpimorphisms :=
  @Functor.preservesEpimorphisms_comp _ _ _ _ _ _ _ _ preservesEpimorphisms_ι_objectProperty
    (@Functor.preservesEpimorphisms_comp _ _ _ _ _ _ _ _
      preservesEpimorphisms_forget_frobeniusPullback preservesEpimorphisms_adicSheafForget)

variable (k₀ l) in
/-- The stalk functor `F ↦ F_s = Γ(Spec k̄, s^* F)` at a geometric point `s` of `X̄`. -/
noncomputable def stalkFunctor
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    WeilSheaf k₀ l X ⥤ WeilCoefficients.{u} l :=
  sheafFunctor k₀ l X ⋙ (s)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ _

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)

/-- The stalk functor preserves monomorphisms. -/
instance preservesMonomorphisms_stalkFunctor : (stalkFunctor k₀ l s).PreservesMonomorphisms := by
  unfold stalkFunctor
  infer_instance

/-- The stalk functor preserves epimorphisms: the global sections on `Spec k̄` are exact. -/
instance preservesEpimorphisms_stalkFunctor : (stalkFunctor k₀ l s).PreservesEpimorphisms := by
  unfold stalkFunctor
  infer_instance

/-- The stalk functor is additive. -/
instance additive_stalkFunctor
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (stalkFunctor k₀ l s).Additive := by
  have : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of (AlgebraicClosure k₀))))
      (WeilCoefficients.{u} l)).Additive := Functor.additive_of_preserves_binary_products _
  have : (sheafFunctor k₀ l X).Additive := inferInstanceAs
    (ObjectProperty.ι _ ⋙ IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _).Additive
  unfold stalkFunctor
  infer_instance

end Functor

variable {F G : WeilSheaf k₀ l X}
  (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)

/-- The map `F_s ⟶ G_s` induced on the stalks at a geometric point `s` by a morphism
`f : F ⟶ G` of Weil sheaves. -/
noncomputable def stalkMap (f : F ⟶ G) : F.stalkObj s ⟶ G.stalkObj s :=
  (stalkFunctor k₀ l s).map f

instance mono_stalkMap (f : F ⟶ G) [Mono f] : Mono (stalkMap s f) :=
  (stalkFunctor k₀ l s).map_mono f

instance epi_stalkMap (f : F ⟶ G) [Epi f] : Epi (stalkMap s f) :=
  (stalkFunctor k₀ l s).map_epi f

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The iterated Weil structure `φ_m : (Frᵐ)^* F ≅ F` is natural in `F`. -/
theorem frobeniusPowIso_hom_naturality (f : F ⟶ G) (m : ℕ) :
    (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.inv)_*ᵃ[l].map
      f.hom.hom.f ≫ (G.frobeniusPowIso m).hom =
      (F.frobeniusPowIso m).hom ≫ f.hom.hom.f := by
  induction m with
  | zero =>
    simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, NatTrans.naturality_assoc,
      NatTrans.naturality, Functor.id_map]
    exact (Category.assoc _ _ _).symm
  | succ m ih =>
    simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Category.assoc, Iso.symm_hom,
      Functor.mapIso_hom, NatTrans.naturality_assoc]
    congr 2
    rw [Functor.comp_map, ← Functor.map_comp_assoc, ih, Functor.map_comp_assoc]
    congr 1
    simp only [IsoAlgebra.str_hom]
    exact f.hom.hom.h

/-- A naturality square for a composite `Γ(c ≫ T(ι ≫ Φ))` of natural isomorphisms `c`, `ι` and
a family `Φ` commuting with `φ`. Stated for general functors, so that it applies to the stalk
isomorphisms without unfolding them. -/
private lemma map_comp_map_naturality {C₁ C₃ D : Type*} [Category C₁] [Category C₃]
    [Category D] (Γ' : C₃ ⥤ D) (T : C₁ ⥤ C₃) (T' : C₁ ⥤ C₃) (P : C₁ ⥤ C₁) (L : C₁ ⥤ C₁)
    (c : T' ≅ P ⋙ T) (ι : P ≅ L) {A B : C₁} (φ : A ⟶ B) (ΦA : L.obj A ⟶ A)
    (ΦB : L.obj B ⟶ B) (h : L.map φ ≫ ΦB = ΦA ≫ φ) :
    Γ'.map (T'.map φ) ≫ Γ'.map (c.hom.app B ≫ T.map (ι.hom.app B ≫ ΦB)) =
      Γ'.map (c.hom.app A ≫ T.map (ι.hom.app A ≫ ΦA)) ≫ Γ'.map (T.map φ) := by
  simp only [← Functor.map_comp, Category.assoc, NatTrans.naturality_assoc, Functor.comp_map]
  congr 2
  simp only [Functor.map_comp, h]

/-- The naturality of the isomorphism `Γ(σ^* t^* A) ≅ Γ(t^* A)` for an automorphism `σ` of
`Spec R`. -/
private lemma globalSections_upperStar_naturality {R : CommRingCat.{u}} {Z : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)} (φ : A ⟶ B)
    (t : Spec R ⟶ Z) (σ : Spec R ≅ Spec R) :
    (Sheaf.Γ _ _).map ((σ.hom ≫ t)^*[WeilCoefficients.{u} l].map φ) ≫
      ((Sheaf.Γ _ _).mapIso ((ProEtale.upperStarComp _ σ.hom t).app B) ≪≫
        (ProEtale.globalSectionsUpperStarIso _ σ).app ((t)^*[_].obj B)).hom =
    ((Sheaf.Γ _ _).mapIso ((ProEtale.upperStarComp _ σ.hom t).app A) ≪≫
        (ProEtale.globalSectionsUpperStarIso _ σ).app ((t)^*[_].obj A)).hom ≫
      (Sheaf.Γ _ _).map ((t)^*[WeilCoefficients.{u} l].map φ) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, ← Functor.map_comp_assoc,
    NatTrans.naturality, Functor.comp_map, Category.assoc]
  rw [Functor.map_comp, Category.assoc]
  congr 1
  exact (ProEtale.globalSectionsUpperStarIso _ σ).hom.naturality _

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
private theorem stalkObjFrobeniusPowIso_hom_eq (m : ℕ) :
    (F.stalkObjFrobeniusPowIso m s).hom =
      (Sheaf.Γ _ _).map ((ProEtale.upperStarComp _ s
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom).hom.app
          F.obj.carrier.X ≫
        (s)^*[_].map ((ProEtale.upperStarIsoLowerStarInv _
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso).hom.app
            F.obj.carrier.X ≫
            (ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso m).hom)) :=
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The isomorphism `F_{s ≫ Frᵐ} ≅ F_s` is natural in `F`. -/
theorem stalkObjFrobeniusPowIso_hom_naturality (f : F ⟶ G) (m : ℕ) :
    stalkMap (s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom) f ≫
      (G.stalkObjFrobeniusPowIso m s).hom =
      (F.stalkObjFrobeniusPowIso m s).hom ≫ stalkMap s f := by
  rw [stalkObjFrobeniusPowIso_hom_eq, stalkObjFrobeniusPowIso_hom_eq]
  -- the objects are given as `F.obj.carrier`, matching the stalks, to keep the kernel fast
  exact map_comp_map_naturality (Sheaf.Γ (Scheme.ProEt.topology _) (WeilCoefficients.{u} l))
    ((s)^*[WeilCoefficients.{u} l])
    ((s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)^*[
      WeilCoefficients.{u} l]) _ _
    (ProEtale.upperStarComp _ s
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)
    (ProEtale.upperStarIsoLowerStarInv _
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso)
    (A := F.obj.carrier.X) (B := G.obj.carrier.X) f.hom.hom.f.hom
    ((ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso m).hom)
    ((ProEtale.AdicSheaf.forget _).map (G.frobeniusPowIso m).hom)
    (by
      have h := congrArg (ProEtale.AdicSheaf.forget _).map (frobeniusPowIso_hom_naturality f m)
      simp only [Functor.map_comp] at h
      exact h)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The isomorphism `F_{σᵐ ≫ s} ≅ F_s` is natural in `F`. -/
theorem stalkObjSpecFrobeniusPowIso_hom_naturality (f : F ⟶ G) (m : ℕ) :
    stalkMap ((specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) f ≫
      (G.stalkObjSpecFrobeniusPowIso m s).hom =
      (F.stalkObjSpecFrobeniusPowIso m s).hom ≫ stalkMap s f :=
  globalSections_upperStar_naturality (φ := f.hom.hom.f.hom) (t := s)
    (specGeometricFrobenius k₀ ^ m).asIso

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The identification of the stalks at equal geometric points is natural. -/
theorem eqToHom_comp_stalkMap {t t' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (h : t = t') (f : F ⟶ G) :
    eqToHom (congrArg F.stalkObj h) ≫ stalkMap t' f =
      stalkMap t f ≫ eqToHom (congrArg G.stalkObj h) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The isomorphism `F_s ≅ F_s` underlying the Frobenius of the stalk
`AlgebraicGeometry.WeilSheaf.stalkAt` is natural in `F`. -/
theorem stalkAt_iso_naturality (f : F ⟶ G) (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s).hom ≫ stalkMap s f =
      stalkMap s f ≫
        ((G.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg G.stalkObj hs.symm) ≪≫
          G.stalkObjFrobeniusPowIso m s).hom := by
  have h1 := stalkObjFrobeniusPowIso_hom_naturality s f m
  have h2 := eqToHom_comp_stalkMap hs.symm f
  have h3 := stalkObjSpecFrobeniusPowIso_hom_naturality s f m
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  have h3' : (F.stalkObjSpecFrobeniusPowIso m s).inv ≫
      stalkMap ((specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) f =
        stalkMap s f ≫ (G.stalkObjSpecFrobeniusPowIso m s).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h3, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [Category.assoc, Category.assoc, ← h1, ← Category.assoc (eqToHom _), h2, Category.assoc,
    ← Category.assoc (F.stalkObjSpecFrobeniusPowIso m s).inv, h3', Category.assoc]

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
private theorem linearEquivOfIso_apply {M N : WeilCoefficients.{u} l} (e : M ≅ N)
    (x : (WeilCoefficients.toModuleCat l).obj M) :
    WeilCoefficients.linearEquivOfIso e x = ((WeilCoefficients.toModuleCat l).map e.hom).hom x :=
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
private theorem stalkAt_frobenius_eq (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    (F.stalkAt s m hs).frobenius = WeilCoefficients.linearEquivOfIso
      ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s) :=
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
private theorem stalkAt_frobenius_apply (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) (x : (F.stalkAt s m hs).carrier) :
    (F.stalkAt s m hs).frobenius x = ((WeilCoefficients.toModuleCat l).map
      ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s).hom).hom x :=
  (LinearEquiv.congr_fun (stalkAt_frobenius_eq s m hs) x).trans (linearEquivOfIso_apply _ x)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The map induced by a morphism `f : F ⟶ G` on the stalks at a geometric point `s`
commutes with the Frobenius of the stalks. -/
theorem stalkAt_frobenius_map (f : F ⟶ G) (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) (x : (F.stalkAt s m hs).carrier) :
    ((WeilCoefficients.toModuleCat l).map (stalkMap s f)).hom
        ((F.stalkAt s m hs).frobenius x) =
      (G.stalkAt s m hs).frobenius
        (((WeilCoefficients.toModuleCat l).map (stalkMap s f)).hom x) := by
  have := congrArg (fun g ↦ ((WeilCoefficients.toModuleCat l).map g).hom x)
    (stalkAt_iso_naturality s f m hs)
  simp only [Functor.map_comp, ModuleCat.hom_comp] at this
  exact (congrArg _ (stalkAt_frobenius_apply s m hs x)).trans
    (this.trans (stalkAt_frobenius_apply (F := G) s m hs _).symm)

/-- The map induced on the stalks by a monomorphism is injective. -/
theorem injective_stalkMap (f : F ⟶ G) [Mono f] :
    Function.Injective ((WeilCoefficients.toModuleCat l).map (stalkMap s f)).hom :=
  (ModuleCat.mono_iff_injective (stalkMap s f)).1 inferInstance

/-- The map induced on the stalks by an epimorphism is surjective. -/
theorem surjective_stalkMap (f : F ⟶ G) [Epi f] :
    Function.Surjective ((WeilCoefficients.toModuleCat l).map (stalkMap s f)).hom :=
  (ModuleCat.epi_iff_surjective (stalkMap s f)).1 inferInstance

section StalkAt

variable (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
  (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)

/-- The map induced by `f : F ⟶ G` on the stalks at `s`, as a linear map between the underlying
spaces of the Frobenius modules `AlgebraicGeometry.WeilSheaf.stalkAt`. -/
noncomputable def stalkAtMap (f : F ⟶ G) :
    (F.stalkAt s m hs).carrier →ₗ[PadicAlgCl l] (G.stalkAt s m hs).carrier :=
  ((WeilCoefficients.toModuleCat l).map (stalkMap s f)).hom

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
theorem stalkAtMap_apply (f : F ⟶ G) (x : (F.stalkAt s m hs).carrier) :
    stalkAtMap s m hs f x = ((WeilCoefficients.toModuleCat l).map (stalkMap s f)).hom x :=
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The map induced on the stalks commutes with the Frobenius. -/
theorem stalkAtMap_frobenius (f : F ⟶ G) (x : (F.stalkAt s m hs).carrier) :
    stalkAtMap s m hs f ((F.stalkAt s m hs).frobenius x) =
      (G.stalkAt s m hs).frobenius (stalkAtMap s m hs f x) :=
  -- passing through `stalkAtMap_apply` explicitly keeps the kernel check fast
  (stalkAtMap_apply s m hs f _).trans ((stalkAt_frobenius_map s f m hs x).trans
    (congrArg (G.stalkAt s m hs).frobenius (stalkAtMap_apply s m hs f x).symm))

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
theorem stalkAtMap_comp {F G H : WeilSheaf k₀ l X} (f : F ⟶ G) (g : G ⟶ H)
    (x : (F.stalkAt s m hs).carrier) :
    stalkAtMap s m hs (f ≫ g) x = stalkAtMap s m hs g (stalkAtMap s m hs f x) := by
  simp only [stalkAtMap, stalkMap, Functor.map_comp]
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
theorem stalkAtMap_id (F : WeilSheaf k₀ l X) (x : (F.stalkAt s m hs).carrier) :
    stalkAtMap s m hs (𝟙 F) x = x := by
  rw [stalkAtMap, stalkMap, (stalkFunctor k₀ l s).map_id F]
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
theorem stalkAtMap_add {F G : WeilSheaf k₀ l X} (f g : F ⟶ G)
    (x : (F.stalkAt s m hs).carrier) :
    stalkAtMap s m hs (f + g) x = stalkAtMap s m hs f x + stalkAtMap s m hs g x := by
  simp only [stalkAtMap, stalkMap, Functor.map_add]
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
theorem stalkAtMap_zero {F G : WeilSheaf k₀ l X} (x : (F.stalkAt s m hs).carrier) :
    stalkAtMap s m hs (0 : F ⟶ G) x = 0 := by
  rw [stalkAtMap, stalkMap, (stalkFunctor k₀ l s).map_zero]
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The stalk of a direct sum is the direct sum of the stalks, with the diagonal Frobenius. -/
theorem nonempty_equiv_stalkAt_biprod (F G : WeilSheaf k₀ l X) :
    Nonempty (((F ⊞ G).stalkAt s m hs).Equiv ((F.stalkAt s m hs).prod (G.stalkAt s m hs))) := by
  refine ⟨⟨LinearEquiv.ofLinearMap
    ((stalkAtMap s m hs biprod.fst).prod (stalkAtMap s m hs biprod.snd))
    ((stalkAtMap s m hs biprod.inl).coprod (stalkAtMap s m hs biprod.inr)) ?_ ?_, fun x ↦ ?_⟩⟩
  · refine LinearMap.ext fun ⟨a, b⟩ ↦ Prod.ext ?_ ?_
    · change stalkAtMap s m hs biprod.fst
        (stalkAtMap s m hs biprod.inl a + stalkAtMap s m hs biprod.inr b) = a
      rw [map_add, ← stalkAtMap_comp, ← stalkAtMap_comp, biprod.inl_fst, biprod.inr_fst,
        stalkAtMap_id, stalkAtMap_zero, add_zero]
    · change stalkAtMap s m hs biprod.snd
        (stalkAtMap s m hs biprod.inl a + stalkAtMap s m hs biprod.inr b) = b
      rw [map_add, ← stalkAtMap_comp, ← stalkAtMap_comp, biprod.inl_snd, biprod.inr_snd,
        stalkAtMap_id, stalkAtMap_zero, zero_add]
  · refine LinearMap.ext fun y ↦ ?_
    change stalkAtMap s m hs biprod.inl (stalkAtMap s m hs biprod.fst y) +
      stalkAtMap s m hs biprod.inr (stalkAtMap s m hs biprod.snd y) = y
    rw [← stalkAtMap_comp, ← stalkAtMap_comp, ← stalkAtMap_add, biprod.total, stalkAtMap_id]
  · exact Prod.ext (stalkAtMap_frobenius s m hs _ x) (stalkAtMap_frobenius s m hs _ x)

theorem injective_stalkAtMap (f : F ⟶ G) [Mono f] : Function.Injective (stalkAtMap s m hs f) :=
  fun a b h ↦ injective_stalkMap s f
    ((stalkAtMap_apply s m hs f a).symm.trans (h.trans (stalkAtMap_apply s m hs f b)))

theorem surjective_stalkAtMap (f : F ⟶ G) [Epi f] :
    Function.Surjective (stalkAtMap s m hs f) := fun y ↦ by
  obtain ⟨x, hx⟩ := surjective_stalkMap s f y
  exact ⟨x, (stalkAtMap_apply s m hs f x).trans hx⟩

/-- The stalk of a subobject of `G` at `s` is a Frobenius-stable subspace of the stalk of `G`, so
it is pure if the stalk of `G` is. -/
theorem stalkAt_isPureOfWeight_of_mono {ι : PadicAlgCl l →+* ℂ} {q : ℕ} {w : ℝ} (f : F ⟶ G)
    [Mono f] (h : (G.stalkAt s m hs).IsPureOfWeight ι q w) :
    (F.stalkAt s m hs).IsPureOfWeight ι q w :=
  FrobeniusModule.IsPureOfWeight.of_injective _ (stalkAtMap_frobenius s m hs f)
    (injective_stalkAtMap s m hs f) h

/-- The stalk of a quotient of `F` at `s` is a Frobenius-equivariant quotient of the stalk of
`F`, so it is pure if the stalk of `F` is. -/
theorem stalkAt_isPureOfWeight_of_epi {ι : PadicAlgCl l →+* ℂ} {q : ℕ} {w : ℝ} (f : F ⟶ G)
    [Epi f] (h : (F.stalkAt s m hs).IsPureOfWeight ι q w) :
    (G.stalkAt s m hs).IsPureOfWeight ι q w :=
  FrobeniusModule.IsPureOfWeight.of_surjective _ (stalkAtMap_frobenius s m hs f)
    (surjective_stalkAtMap s m hs f) h

end StalkAt

/-- A subobject of a punctually `ι`-pure Weil sheaf of weight `w` is punctually `ι`-pure of
weight `w`: its stalks are Frobenius-stable subspaces. -/
theorem IsPunctuallyPureOfWeight.of_mono {ι : PadicAlgCl l →+* ℂ} {w : ℝ} (f : F ⟶ G) [Mono f]
    (h : G.IsPunctuallyPureOfWeight ι w) : F.IsPunctuallyPureOfWeight ι w := fun x ↦
  stalkAt_isPureOfWeight_of_mono _ _ _ f (h x)

/-- A quotient of a punctually `ι`-pure Weil sheaf of weight `w` is punctually `ι`-pure of
weight `w`: its stalks are Frobenius-equivariant quotients. -/
theorem IsPunctuallyPureOfWeight.of_epi {ι : PadicAlgCl l →+* ℂ} {w : ℝ} (f : F ⟶ G) [Epi f]
    (h : F.IsPunctuallyPureOfWeight ι w) : G.IsPunctuallyPureOfWeight ι w := fun x ↦
  stalkAt_isPureOfWeight_of_epi _ _ _ f (h x)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The stalk of a direct sum is the direct sum of the stalks, with the diagonal Frobenius. -/
theorem nonempty_equiv_stalk_biprod (F G : WeilSheaf k₀ l X) (x : X.finitePoints) :
    Nonempty (((F ⊞ G).stalk x).Equiv ((F.stalk x).prod (G.stalk x))) :=
  nonempty_equiv_stalkAt_biprod _ _ _ F G

/-- The support of a quotient of `F` is contained in the support of `F`: the stalks of the
quotient are quotients of the stalks of `F`. -/
theorem support_subset_of_epi (f : F ⟶ G) [Epi f] : G.support ⊆ F.support := fun x hx ↦
  have : Nontrivial (G.stalk x).carrier := hx
  Function.Surjective.nontrivial (β := (G.stalk x).carrier) (surjective_stalkAtMap _ _ _ f)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A zero Weil sheaf has empty support: its stalks are zero. -/
theorem support_eq_empty_of_isZero (hF : IsZero F) : F.support = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x (hx : Nontrivial (F.stalk x).carrier) ↦ ?_
  have hz : IsZero ((WeilCoefficients.toModuleCat l).obj ((Sheaf.Γ _ _).obj
      ((((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x))^*[_].obj
        ((ProEtale.AdicSheaf.forget _).obj ((IsoAlgebra.forget _).obj
          ((ObjectProperty.ι _).obj F)))))) :=
    (WeilCoefficients.toModuleCat l).map_isZero <| (Sheaf.Γ _ _).map_isZero <|
      Functor.map_isZero _ <| (ProEtale.AdicSheaf.forget _).map_isZero <|
        (IsoAlgebra.forget _).map_isZero <| (ObjectProperty.ι _).map_isZero hF
  have : Subsingleton (F.stalk x).carrier := ModuleCat.subsingleton_of_isZero hz
  exact not_subsingleton _ this

end AlgebraicGeometry.WeilSheaf
