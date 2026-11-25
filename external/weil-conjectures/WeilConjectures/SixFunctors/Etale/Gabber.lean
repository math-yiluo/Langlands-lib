/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.AlgebraicGeometry.ConstantModuleSheavesForgetColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.InjectiveModuleAnnihilatorAcyclic
import WeilConjectures.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity
import WeilConjectures.AlgebraicGeometry.CofilteredEtaleCohomologyCocone
import WeilConjectures.AlgebraicGeometry.ConstructibleRestrictionClass
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyFilteredColimit

/-!
# Gabber's affine comparison theorem

Let `(A, I)` be a henselian pair (`HenselianRing A I`), `T = Spec A` and `T₀ = Spec (A ⧸ I)`
with its closed immersion `i : T₀ ⟶ T`. For every torsion étale sheaf `F` on `T` the
restriction `Hᵠ(T, F) ⟶ Hᵠ(T₀, F|_{T₀})` is bijective for every `q` [Stacks 09ZI].

The coefficient sheaves are sheaves of `Λ`-modules with torsion geometric stalks
(`AlgebraicGeometry.Scheme.IsTorsionModuleSheaf`), and `Hᵠ` is the cohomology of the underlying
abelian sheaf, the restriction map being `AlgebraicGeometry.Etale.cohomologyMap i`.

The proof is by induction on `q`. The degree-zero case is the henselian restriction lemma
(`AlgebraicGeometry.Etale.bijective_cohomologyMap_zero_of_henselianRing`). In positive degree
classes are effaced by monomorphisms into torsion sheaves
(`AlgebraicGeometry.Etale.exists_mono_map_eq_zero_of_henselianRing`), and a diagram chase in
the long exact cohomology sequences of `0 ⟶ F ⟶ F' ⟶ F'/F ⟶ 0` on `T` and on `T₀` concludes.
The effacement proof first represents a class by bounded module coefficients using filtered
colimits. Bounded abelian surjectivity lifts that class to the affine scheme. An injective
presentation of the bounded module sheaf factors through the kernel of multiplication by
its annihilating integer; this kernel is torsion and has acyclic underlying abelian
cohomology. Pushing out this monomorphism along the map to `F` kills the original class.
The bounded surjectivity remains a separate theorem item; annihilator acyclicity is proved.
The former follows the finite-coefficient 09ZE/09ZI argument independently of this module.
The false arbitrary-constructible finite-cover statement has been retired.

## Main statements

- `AlgebraicGeometry.Etale.exists_cohomologyMap_eq_zero_of_isLimit`: a class that dies on a
  cofiltered limit dies at a finite stage.
- `AlgebraicGeometry.Etale.exists_isConstructibleSheaf_hom_of_henselianRing`: a class comes
  from a constructible sheaf mapping to `F`.
- `AlgebraicGeometry.Etale.exists_mono_map_eq_zero_of_henselianRing`: effacement.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_of_henselianRing`: Gabber's theorem.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Auxiliary

/-! ### Auxiliary lemmas -/

/-- The comparison map on cohomology commutes with the maps induced by morphisms of
sheaves. -/
lemma cohomologyMap_comp_mk₀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G G' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : G ⟶ G') {n : ℕ}
    (x : Sheaf.H G n) :
    cohomologyMap f G' n (x.comp (Ext.mk₀ φ) (add_zero n)) =
      (cohomologyMap f G n x).comp (Ext.mk₀ (((f)^*[AddCommGrpCat.{u + 1}]).map φ))
        (add_zero n) :=
  cohomologyMap_map f n φ x

/-- The comparison map on cohomology commutes with the connecting maps of a short exact
sequence. -/
lemma cohomologyMap_comp_extClass {X Y : Scheme.{u}} (f : X ⟶ Y)
    {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    {n : ℕ} (x : Sheaf.H S.X₃ n) :
    cohomologyMap f S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (cohomologyMap f S.X₃ n x).comp
        (hS.map_of_exact ((f)^*[AddCommGrpCat.{u + 1}])).extClass rfl := by
  rw [cohomologyMap_apply, cohomologyMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

/-- Taking underlying abelian sheaves of sheaves of `Λ`-modules is additive. -/
instance additive_sheafCompose_forget₂ {X : Scheme.{u}} :
    (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).Additive where
  map_add := by
    intros
    rfl

/-- Taking underlying abelian sheaves of sheaves of `Λ`-modules is left exact: it commutes
with `sheafToPresheaf`, which creates limits, and `forget₂` preserves limits. -/
instance preservesFiniteLimits_sheafCompose_forget₂ {X : Scheme.{u}} :
    PreservesFiniteLimits (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  have : PreservesFiniteLimits (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- The underlying abelian sheaves of a short exact sequence of sheaves of `Λ`-modules form a
short exact sequence. -/
lemma shortExact_map_forget₂ {X : Scheme.{u}}
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact) :
    (S.map (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).ShortExact := by
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : PreservesColimitsOfSize.{u + 1, u + 1} U :=
    constantModuleSheaves_forget_preservesColimits X Λ
  have : PreservesFiniteColimits U := inferInstance
  exact hS.map_of_exact U

/-- **Henselian restriction in degree zero**: for a henselian pair `(A, I)` and any abelian
sheaf `G` on `Spec A`, restriction `Γ(Spec A, G) ⟶ Γ(Spec (A ⧸ I), G|)` is bijective
[Stacks 09ZH]. This is the affine case of the blueprint lemma
`theorem-comparison-over-henselian-pair-degree--1` (subsection
`theorem-pbc-injective-acyclicity`). -/
theorem bijective_cohomologyMap_zero_of_henselianRing {A : Type u} [CommRing A] (I : Ideal A)
    [HenselianRing A I] (G : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective
      (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) G 0) :=
  (bijective_cohomologyMap_zero_iff _ G).2
    ((isIso_globalSectionsUpperStarMap_iff_bijective_pullSection _ G).2
      (bijective_pullSection_of_henselianRing I (𝟙 _) _ (𝟙 _) IsPullback.of_id_snd G))

end Auxiliary

/-- **Finite-stage killing of a class.** Let `(Dⱼ)` be a cofiltered system of
quasi-compact quasi-separated schemes over `S` with affine transition maps and limit `X`. If
the pullback of a class `x ∈ Hᵠ(S, G)` to `X` vanishes, then its pullback to some `Dⱼ`
vanishes, by the continuity `colimⱼ Hᵠ(Dⱼ, G|) ≅ Hᵠ(X, G|)` of étale cohomology.

The blueprint applies this to the closed fibres `(T_λ)₀` of a system of finite finitely
presented covers `T_λ ⟶ T` of an affine henselian pair `(T, T₀)` whose limit is an integral
strictly local cover, and a torsion sheaf; neither the special shape of the system nor the
torsion hypothesis is used, so they are not assumed here.
-/
theorem exists_cohomologyMap_eq_zero_of_isLimit {J : Type u} [SmallCategory J] [IsCofiltered J]
    {S : Scheme.{u}} (D : J ⥤ Scheme.{u}) (π : D ⟶ (Functor.const J).obj S)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) {q : ℕ} (x : Sheaf.H G q) (j₀ : J)
    (hx : cohomologyMap (c.π.app j₀ ≫ π.app j₀) G q x = 0) :
    ∃ j, cohomologyMap (π.app j) G q x = 0 := by
  obtain ⟨H, eH, r, hr, heH, B, hB, e, he⟩ :=
    exists_cofiltered_etale_cohomology_cocone D π c hc G q j₀
  have hzero : B.ι.app (Opposite.op j₀) (r j₀ x) =
      B.ι.app (Opposite.op j₀) (0 : H.obj (Opposite.op j₀)) := by
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    simpa only [map_zero] using (he j₀ x).trans hx
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨j, f, hf⟩ := (hB.eq_iff' (r j₀ x) 0).mp hzero
  refine ⟨j.unop, ?_⟩
  have hj : r j.unop x = 0 := by
    rw [← hr j.unop j₀ f.unop x]
    simpa only [Quiver.Hom.op_unop, map_zero] using hf
  rw [← heH j.unop x, hj, map_zero]


/-- **Constructible approximation of a class.** Let `(A, I)` be a henselian pair, `Λ` finite
and `F` a sheaf of `Λ`-modules on `Spec A`. Every class `c ∈ Hᵠ(Spec (A ⧸ I), F|)` comes from
a constructible sheaf mapping to `F`, as in the first step of the proof of Gabber's affine
effacement [Stacks 09ZE]: there are a morphism `ι : C ⟶ F` with `C` constructible and a class
`c'` on the closed fibre with coefficients in `C|` mapping to `c`.

The morphism `ι` cannot be required to be a monomorphism: for `A = ∏_ℕ 𝔽₂`, `I = 0`,
`F = x_* ℤ/2` the skyscraper sheaf at a closed non-open point `x` (a non-principal
ultrafilter), `q = 0` and `c = 1`, the only subsheaf of `F` containing `1` is `F` itself, whose
support `{x}` is not constructible. In the Noetherian case, where `F` is the union of its
constructible subsheaves, `ι` can be taken injective. In general the statement follows from
writing `F` as a filtered colimit of constructible sheaves [Stacks 03SA] and from the
commutation of the cohomology of the quasi-compact quasi-separated closed fibre with filtered
colimits [Stacks 03Q5].

The blueprint phrases this with a quasi-compact étale neighbourhood `U ⟶ T` and a cocycle
with values in `C`; since `T` is affine one can take `U = T`, and "the cocycle factors" is
expressed on cohomology classes. Finiteness of `Λ` makes `F` torsion and guarantees that the
sheaf generated by finitely many sections has finite stalks (for an infinite `Λ` such as
`𝐅_p[t]` this fails).
(blueprint: theorem-gabber-affine-proper-base-change)
-/
theorem exists_isConstructibleSheaf_hom_of_henselianRing [Finite Λ] {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I]
    (F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) {q : ℕ}
    (c : Sheaf.H
      (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))^*[AddCommGrpCat.{u + 1}]).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) q) :
    ∃ (C : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ι : C ⟶ F),
      IsConstructibleSheaf C ∧ ∃ c', Sheaf.H.map
        (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))^*[AddCommGrpCat.{u + 1}]).map
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map ι)) q c' =
        c :=
  by
    let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    obtain ⟨e⟩ := exists_upperStar_forget₂_natIso Λ i
    have eH := Functor.isoWhiskerRight e (Sheaf.functorH _ q)
    obtain ⟨C, hC, ι, c', hc'⟩ := exists_constructible_restriction_class i Λ F q
      ((eH.inv.app F) c)
    obtain ⟨S, hCS⟩ := hC
    have hC' : IsConstructibleSheaf C := by
      refine ⟨⟨S, ?_⟩⟩
      intro k
      exact (finite_locally_constant_module_values_iff _).1.mp (hCS k)
    refine ⟨C, ι, hC', (eH.hom.app C) c', ?_⟩
    have hn := ConcreteCategory.congr_hom (eH.hom.naturality ι) c'
    change (eH.hom.app F)
      (Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1})).map ((i)^*[ModuleCat.{u + 1} Λ].map ι)) q c') =
      Sheaf.H.map ((i)^*[AddCommGrpCat.{u + 1}].map
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
          AddCommGrpCat.{u + 1})).map ι)) q ((eH.hom.app C) c') at hn
    rw [← hn, hc']
    exact ConcreteCategory.congr_hom (eH.inv_hom_id_app F) c


private theorem torsion_of_annihilated {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (n : ℕ) (hn : 0 < n) (hG : n • 𝟙 G = 0) : IsTorsionModuleSheaf G where
  isTorsion_sheafFiber Ω _ _ s x := by
    have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
    have h := congrArg ((pointSmallEtale s).sheafFiber.map) hG
    simp only [Functor.map_nsmul, Functor.map_zero] at h
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2
      ⟨n, hn, by simpa using congrArg (fun f ↦ f.hom x) h⟩

private theorem torsion_pushout {X : Scheme.{u}}
    {C E F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : C ⟶ E) (b : C ⟶ F) [IsTorsionModuleSheaf E] [IsTorsionModuleSheaf F] :
    IsTorsionModuleSheaf (pushout a b) := by
  have hEF : IsTorsionModuleSheaf (E ⊞ F) := by
    refine ⟨fun Ω _ _ s x ↦ ?_⟩
    have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
      hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
    let T := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
    let : T.Additive := (pointSmallEtale s).sheafFiber_additive
    let : PreservesBinaryBiproduct E F T :=
      preservesBinaryBiproduct_of_preservesBiproduct T E F
    have hE : IsAddTorsion (T.obj E) := IsTorsionModuleSheaf.isTorsion_sheafFiber Ω s
    have hF : IsAddTorsion (T.obj F) := IsTorsionModuleSheaf.isTorsion_sheafFiber Ω s
    let e := (T.mapBiprod E F) ≪≫ ModuleCat.biprodIsoProd (T.obj E) (T.obj F)
    exact IsAddTorsion.of_surjective (f := e.inv.hom.toAddMonoidHom)
      e.toLinearEquiv.symm.surjective
      (fun y ↦ IsOfFinAddOrder.prod_mk (hE y.1) (hF y.2)) x
  have : Epi (biprod.desc (pushout.inl a b) (pushout.inr a b)) :=
    (IsPushout.of_hasPushout a b).epi_shortComplex_g
  exact IsTorsionModuleSheaf.of_epi (biprod.desc (pushout.inl a b) (pushout.inr a b))

private theorem bounded_restriction_representative {A : Type u} [CommRing A]
    (I : Ideal A)
    (F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ)
    (c : Sheaf.H
      (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))^*[AddCommGrpCat.{u + 1}]).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) q) :
    ∃ (G : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (b : G ⟶ F) (n : ℕ), 0 < n ∧ n • 𝟙 G = 0 ∧
      ∃ z, Sheaf.H.map
        (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))^*[AddCommGrpCat.{u + 1}]).map
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map b)) q z =
        c := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let V := (i)^*[AddCommGrpCat.{u + 1}]
  have : V.IsLeftAdjoint :=
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).isLeftAdjoint
  obtain ⟨J, hJ, hfiltered, D, d, hd, rfl, hD⟩ := IsTorsionModuleSheaf.exists_isColimit Λ F
  let e := ULiftHomULiftCategory.equiv.{u, u} J
  have : IsFiltered (ULiftHom.{u} (ULift.{u} J)) := IsFiltered.of_equivalence e
  let d' := d.whisker e.inverse
  have hd' : IsColimit d' := (Functor.Final.isColimitWhiskerEquiv e.inverse d).symm hd
  have : PreservesColimitsOfSize.{u + 1, u + 1} U :=
    constantModuleSheaves_forget_preservesColimits X Λ
  have : PreservesColimitsOfSize.{u, u} U :=
    preservesColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} U
  have : PreservesColimitsOfSize.{u + 1, u} U :=
    preservesColimitsOfSize_of_univLE.{u + 1, u + 1, u + 1, u} U
  let a := V.mapCocone (U.mapCocone d')
  have ha : IsColimit a := isColimitOfPreserves V (isColimitOfPreserves U hd')
  obtain ⟨hH⟩ := Scheme.etaleCohomology_isColimit_of_isFiltered Z ha q
  obtain ⟨eH⟩ := Scheme.nonempty_sheafH_extDerivedIso Z q
  have hHH : IsColimit ((Sheaf.functorH Z.smallEtaleTopology q).mapCocone a) :=
    IsColimit.mapCoconeEquiv eH.symm hH
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨j, z, hz⟩ := Concrete.isColimit_exists_rep _ hHH c
  obtain ⟨n, hn, hGn⟩ := hD (e.inverse.obj j)
  exact ⟨D.obj (e.inverse.obj j), d.ι.app (e.inverse.obj j), n, hn, hGn, z, hz⟩

/-- **Affine Gabber effacement.** Let `(A, I)` be a henselian pair and `F` a torsion sheaf of
`Λ`-modules on `T = Spec A`. Every class `c ∈ Hᵠ(T₀, F|)` of positive degree on
`T₀ = Spec (A ⧸ I)` is killed by some monomorphism `F ⟶ F'` into a torsion sheaf.
(blueprint: theorem-gabber-affine-proper-base-change)
-/
theorem exists_mono_map_eq_zero_of_henselianRing {A : Type u} [CommRing A] (I : Ideal A)
    [HenselianRing A I] (F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] {q : ℕ} (hq : 0 < q)
    (c : Sheaf.H
      (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))^*[AddCommGrpCat.{u + 1}]).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) q) :
    ∃ (F' : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ι : F ⟶ F'),
      IsTorsionModuleSheaf F' ∧ Mono ι ∧ Sheaf.H.map
        (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))^*[AddCommGrpCat.{u + 1}]).map
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map ι)) q c =
        0 := by
  let X := Spec (.of A)
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let V := (i)^*[AddCommGrpCat.{u + 1}]
  have : V.IsLeftAdjoint :=
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).isLeftAdjoint
  obtain ⟨G, b, n, hn, hGn, z, hz⟩ := bounded_restriction_representative Λ I F q c
  let J := Injective.under G
  let E := kernel (n • 𝟙 J)
  have hlift : Injective.ι G ≫ (n • 𝟙 J) = 0 := by
    rw [Preadditive.comp_nsmul, Category.comp_id, ← Category.id_comp (Injective.ι G),
      ← Preadditive.nsmul_comp, hGn, zero_comp]
  let a : G ⟶ E := kernel.lift _ (Injective.ι G) hlift
  have ha : Mono a := mono_of_mono_fac (kernel.lift_ι _ _ hlift)
  have hEn : n • 𝟙 E = 0 := by
    rw [← cancel_mono (kernel.ι (n • 𝟙 J)), Preadditive.nsmul_comp, Category.id_comp,
      zero_comp, ← Category.comp_id (kernel.ι _), ← Preadditive.comp_nsmul, kernel.condition]
  have hE : IsTorsionModuleSheaf E := torsion_of_annihilated Λ E n hn hEn
  have hUGn : n • 𝟙 (U.obj G) = 0 := by
    have hid : U.map (𝟙 G) = 𝟙 (U.obj G) := U.map_id G
    simpa only [Functor.map_nsmul, Functor.map_zero, hid] using congrArg U.map hGn
  obtain ⟨x, hx⟩ := surjective_cohomologyMap_of_henselianRing_of_nsmul_eq_zero I
    (U.obj G) n hn hUGn q z
  have hzero : Sheaf.H.map (V.map (U.map a)) q z = 0 := by
    rw [← hx, ← cohomologyMap_map]
    have hsub := subsingleton_H_kernel_nsmul_injective_module Λ X J n hn q hq
    rw [hsub.elim (Sheaf.H.map (U.map a) q x) 0, map_zero]
  have hP : IsTorsionModuleSheaf (pushout a b) := torsion_pushout Λ a b
  refine ⟨pushout a b, pushout.inr a b, hP, inferInstance, ?_⟩
  rw [← hz, ← Sheaf.H.map_comp_apply, ← Functor.map_comp, ← Functor.map_comp,
    ← pushout.condition, Functor.map_comp, Functor.map_comp, Sheaf.H.map_comp_apply,
    hzero, map_zero]

/-- **Gabber's affine comparison theorem.** Let `(A, I)` be a henselian pair and `F` a
torsion sheaf of `Λ`-modules on `T = Spec A`. The restriction to `T₀ = Spec (A ⧸ I)` induces
bijections `Hᵠ(T, F) ⟶ Hᵠ(T₀, F|_{T₀})` for all `q`.

The blueprint's "detailed form" also asserts this for affine schemes of finite type over `A`
in place of `Spec A`; that relative version is false (for `A = k⟦t⟧` and `X = 𝔸¹_A` the class
of the Artin–Schreier cover `y^p - y = t x` is nonzero on `X` but vanishes on the closed
fibre), so only the pair form, which is [Stacks 09ZI], is stated.
(blueprint: theorem-gabber-affine-proper-base-change)
(blueprint: theorem-gabber-affine-proper-base-change)
-/
@[stacks 09ZI]
theorem bijective_cohomologyMap_of_henselianRing {A : Type u} [CommRing A] (I : Ideal A)
    [HenselianRing A I] (F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    Function.Bijective (cohomologyMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  induction q generalizing F with
  | zero => exact bijective_cohomologyMap_zero_of_henselianRing I _
  | succ n ih =>
    -- the short exact sequence `0 ⟶ F ⟶ F' ⟶ F'/F ⟶ 0` attached to a monomorphism
    have key {F' : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ι : F ⟶ F')
        [Mono ι] : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
      { exact := ShortComplex.exact_cokernel ι }
    refine ⟨?_, fun η ↦ ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro ξ hξ
      -- efface `ξ` on `T` itself, through the henselian pair `(A, ⊥)`
      have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A))) :=
        (ConcreteCategory.isIso_iff_bijective _).2
          ⟨fun a b h ↦ by simpa [Ideal.Quotient.eq, sub_eq_zero] using h,
            Ideal.Quotient.mk_surjective⟩
      obtain ⟨F', ι, hF', hι, hξι⟩ := exists_mono_map_eq_zero_of_henselianRing Λ
        (⊥ : Ideal A) F n.succ_pos (cohomologyMap _ _ _ ξ)
      rw [← cohomologyMap_map] at hξι
      replace hξι := (cohomologyMap_bijective _ _ _).1 (hξι.trans (map_zero _).symm)
      let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
      have hS : (S.map (sheafCompose _
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).ShortExact :=
        shortExact_map_forget₂ Λ (key ι)
      have : IsTorsionModuleSheaf (cokernel ι) := IsTorsionModuleSheaf.of_epi (cokernel.π ι)
      obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS ξ hξι rfl
      replace hξ := (cohomologyMap_comp_extClass _ hS z).symm.trans hξ
      obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₃ _
        (hS.map_of_exact ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))^*[_])) _ rfl hξ
      obtain ⟨v, rfl⟩ := (ih F').2 w
      have hvz : v.comp (Ext.mk₀ (S.map (sheafCompose _
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).g) (add_zero n) = z :=
        (ih (cokernel ι)).1 ((cohomologyMap_comp_mk₀ _ _ v).trans hw)
      rw [← hvz, Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) (by omega)]
      exact (congrArg (fun t ↦ v.comp t (show n + 1 = n + 1 from rfl)) hS.comp_extClass).trans
        (Ext.comp_zero _ _ _ _ _)
    · obtain ⟨F', ι, hF', hι, hη⟩ := exists_mono_map_eq_zero_of_henselianRing Λ I F n.succ_pos η
      let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
      have hS : (S.map (sheafCompose _
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).ShortExact :=
        shortExact_map_forget₂ Λ (key ι)
      have : IsTorsionModuleSheaf (cokernel ι) := IsTorsionModuleSheaf.of_epi (cokernel.π ι)
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _
        (hS.map_of_exact ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))^*[_])) η hη rfl
      obtain ⟨z, rfl⟩ := (ih (cokernel ι)).2 y
      exact ⟨z.comp hS.extClass rfl, (cohomologyMap_comp_extClass _ hS z).trans hy⟩

end Etale

end AlgebraicGeometry
