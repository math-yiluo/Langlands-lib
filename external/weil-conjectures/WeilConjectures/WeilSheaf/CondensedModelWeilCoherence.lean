/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelWeil
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobeniusNaturality

/-!
# The two Weil structures on a pulled-back object agree

Let `k` be a finite field, `f : X₀ ⟶ Spec k`, `p : X̄ ⟶ X₀` the projection of the geometric
fibre, `Fr_X = 𝟙 × σ` the geometric Galois Frobenius of `X̄`, `Φ = Φ₀ × 𝟙` the scheme
Frobenius of `X̄` and `Φ₀` the `q`-power Frobenius of `X₀`. For a module object `M` over `Λ` on
`X₀`, the pullback `p^* M` carries two natural Weil structures:

- for `Fr_X`, `Fr_X^* p^* M ≅ (Fr_X ≫ p)^* M = p^* M`
  (`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeil`);
- for `Φ`, `Φ^* p^* M ≅ (Φ ≫ p)^* M = (p ≫ Φ₀)^* M ≅ p^* Φ₀^* M ≅ p^* M`, through the
  trivialization `Φ₀^* ≅ 𝟭` of the pullback along the absolute Frobenius of `X₀`
  (`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilModelFrobenius`).

We show that they agree under the identification `Φ^* ≅ Fr_X^*` of
`AlgebraicGeometry.ProEtale.CondensedRing.upperStarGeometricFiberFrobeniusIso`. The key input is
the naturality of the absolute Frobenius trivialization under pullback
(`ProEtale.CondensedRing.upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app`).

## Main results

- `AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberProjUpperStarModelFrobeniusIso_eq`:
  the structure isomorphism `p^* ⋙ Φ^* ≅ p^*` of the `Φ`-Weil structure is
  `p^* ⋙ Φ^* ≅ p^* ⋙ Fr_X^* ≅ p^*`.
- `ProEtale.CondensedRing.upperStarComp_symm_trans_isoWhiskerRight_eq_isoWhiskerLeft_trans`:
  the general coherence behind it, for any `p : X ⟶ Y` and compatible trivializations.
- `AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilCompTransportIso`: the transport
  `geometricFiberFrobeniusTransport` along `Φ^* ≅ Fr_X^*` of the `Fr_X`-Weil objects `p^* M`
  (`geometricFiberWeil`) is isomorphic, with identity components, to the `Φ`-Weil objects `p^* M`
  (`geometricFiberWeilModelFrobenius`).
- `CategoryTheory.Endofunctor.IsoAlgebra.functorOfNatIsoCompMapOfNatIsoIso`: the general
  transport of structure isomorphisms along an isomorphism of endofunctors.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A functor `P : C ⥤ D` with an isomorphism `s : P ⋙ G ≅ P` gives the functor `C ⥤ IsoAlgebra G`
sending `c` to `P c` with the structure isomorphism `s_c : G (P c) ≅ P c`. -/
@[simps obj map]
noncomputable def functorOfNatIso {G : D ⥤ D} (P : C ⥤ D) (s : P ⋙ G ≅ P) :
    C ⥤ IsoAlgebra G where
  obj c := mk (P.obj c) (s.app c)
  map φ := ObjectProperty.homMk
    { f := P.map φ
      h := s.hom.naturality φ }

/-- The functor `C ⥤ IsoAlgebra G` of `CategoryTheory.Endofunctor.IsoAlgebra.functorOfNatIso`
composed with the forgetful functor is `P`. -/
lemma functorOfNatIso_comp_forget {G : D ⥤ D} (P : C ⥤ D) (s : P ⋙ G ≅ P) :
    functorOfNatIso P s ⋙ forget G = P :=
  rfl

/-- **Transport of structure isomorphisms along an isomorphism of endofunctors**: for
`e : G ≅ H`, structure isomorphisms `s : P ⋙ H ≅ P` and `t : P ⋙ G ≅ P` with
`t = P ◁ e ≪≫ s`, the `H`-algebras `(P c, s_c)` transported along `e` (that is, along
`mapOfNatIso (λ ≪≫ e ≪≫ ρ⁻¹)`) are the `G`-algebras `(P c, t_c)`, by an isomorphism with
identity underlying morphisms. -/
noncomputable def functorOfNatIsoCompMapOfNatIsoIso {G H : D ⥤ D} (P : C ⥤ D) (e : G ≅ H)
    (s : P ⋙ H ≅ P) (t : P ⋙ G ≅ P) (h : t = Functor.isoWhiskerLeft P e ≪≫ s) :
    functorOfNatIso P s ⋙
        mapOfNatIso (Functor.leftUnitor G ≪≫ e ≪≫ (Functor.rightUnitor H).symm) ≅
      functorOfNatIso P t :=
  NatIso.ofComponents
    (fun c ↦ ObjectProperty.isoMk _ (Algebra.isoMk (Iso.refl _) (by
      subst h
      simp [mapOfNatIso, Algebra.mapOfNatTrans, functorOfNatIso])))
    (fun φ ↦ ObjectProperty.hom_ext _ (Algebra.Hom.ext (by simp [mapOfNatIso])))

/-- The underlying morphisms of the components of
`CategoryTheory.Endofunctor.IsoAlgebra.functorOfNatIsoCompMapOfNatIsoIso` are identities. -/
@[simp]
lemma functorOfNatIsoCompMapOfNatIsoIso_hom_app_hom_f {G H : D ⥤ D} (P : C ⥤ D) (e : G ≅ H)
    (s : P ⋙ H ≅ P) (t : P ⋙ G ≅ P) (h : t = Functor.isoWhiskerLeft P e ≪≫ s) (c : C) :
    ((functorOfNatIsoCompMapOfNatIsoIso P e s t h).hom.app c).hom.f = 𝟙 (P.obj c) :=
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Coherence

variable {X Y Y' Z : Scheme.{u}}

/-- A coherence of the composition isomorphisms of pullbacks: for `a ≫ r = F` and `r ≫ p = q`,
the two isomorphisms `p^* ⋙ F^* ≅ q^* ⋙ a^*`, through `(F ≫ p)^* = (a ≫ q)^*` and through
`F^* = (a ≫ r)^* ≅ r^* ⋙ a^*` and `p^* ⋙ r^* ≅ (r ≫ p)^* = q^*`, agree. -/
@[reassoc]
lemma upperStarComp_inv_app_comp_upperStarCongr_hom_app_comp_upperStarComp_hom_app
    (a : X ⟶ Y) (r : Y ⟶ Y') (p : Y' ⟶ Z) {F : X ⟶ Y'} {q : Y ⟶ Z} (hF : a ≫ r = F)
    (hq : r ≫ p = q) (h : F ≫ p = a ≫ q)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (upperStarComp Λ F p).inv.app M ≫ (upperStarCongr Λ h).hom.app M ≫
        (upperStarComp Λ a q).hom.app M =
      (upperStarCongr Λ hF.symm).hom.app ((p)^*⟦Λ⟧.obj M) ≫
        (upperStarComp Λ a r).hom.app ((p)^*⟦Λ⟧.obj M) ≫
        (a)^*⟦Λ⟧.map ((upperStarComp Λ r p).inv.app M ≫ (upperStarCongr Λ hq).hom.app M) := by
  subst hF hq
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, upperStarCongr_self Λ (rfl : a ≫ r = a ≫ r),
    upperStarCongr_self Λ (rfl : r ≫ p = r ≫ p), Iso.refl_hom, Iso.refl_hom, NatTrans.id_app,
    NatTrans.id_app, Category.comp_id, Category.id_comp,
    upperStarComp_hom_app_comp_upperStarComp_hom_app_assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]


/-- **Comparison of two invariance isomorphisms of a pullback**. Let `p : X ⟶ Y`, endomorphisms
`a, r, F` of `X` and `b` of `Y` with `a ≫ r = F`, `r ≫ p = p`, `F ≫ p = p ≫ b`, and
trivializations `κ_X : a^* ≅ 𝟭`, `κ_Y : b^* ≅ 𝟭` compatible along `p ≫ b = a ≫ p` (`hnat`, the
form of
`ProEtale.CondensedRing.upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app`).
Then the isomorphism `p^* ⋙ F^* ≅ (F ≫ p)^* = (p ≫ b)^* ≅ b^* ⋙ p^* ≅ p^*` through `κ_Y` is
`p^* ⋙ F^* ≅ p^* ⋙ (a ≫ r)^* ≅ p^* ⋙ r^* ⋙ a^* ≅ p^* ⋙ r^* ≅ (r ≫ p)^* = p^*` through `κ_X`. -/
lemma upperStarComp_symm_trans_isoWhiskerRight_eq_isoWhiskerLeft_trans {X Y : Scheme.{u}}
    (p : X ⟶ Y) (a r F : X ⟶ X) (b : Y ⟶ Y) (κX : (a)^*⟦Λ⟧ ≅ 𝟭 _) (κY : (b)^*⟦Λ⟧ ≅ 𝟭 _)
    (hF : a ≫ r = F) (hr : r ≫ p = p) (hp : F ≫ p = p ≫ b) (hab : p ≫ b = a ≫ p)
    (hnat : ∀ M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y),
      (upperStarComp Λ p b).hom.app M ≫ (p)^*⟦Λ⟧.map (κY.hom.app M) =
        (upperStarCongr Λ hab).hom.app M ≫ (upperStarComp Λ a p).hom.app M ≫
          κX.hom.app ((p)^*⟦Λ⟧.obj M)) :
    ((upperStarComp Λ F p).symm ≪≫ upperStarCongr Λ hp ≪≫ upperStarComp Λ p b) ≪≫
        Functor.isoWhiskerRight κY (p)^*⟦Λ⟧ ≪≫ Functor.leftUnitor _ =
      Functor.isoWhiskerLeft (p)^*⟦Λ⟧ (upperStarCongr Λ hF.symm ≪≫ upperStarComp Λ a r ≪≫
          Functor.isoWhiskerLeft (r)^*⟦Λ⟧ κX ≪≫ Functor.rightUnitor _) ≪≫
        ((upperStarComp Λ r p).symm ≪≫ upperStarCongr Λ hr) := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  rw [NatTrans.comp_whiskerRight_leftUnitor_hom_app,
    NatTrans.comp_app (Functor.whiskerLeft (p)^*⟦Λ⟧ _), Functor.whiskerLeft_app,
    NatTrans.comp_comp_whiskerLeft_rightUnitor_hom_app]
  simp only [NatTrans.comp_app, Category.assoc]
  rw [hnat, upperStarCongr_hom_app_trans_assoc,
    upperStarComp_inv_app_comp_upperStarCongr_hom_app_comp_upperStarComp_hom_app_assoc Λ a r p hF
      hr, NatTrans.naturality, Functor.id_map]

end Coherence

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The scheme Frobenius `Φ = Φ₀ × 𝟙` of the geometric fibre lies over the absolute `q`-power
Frobenius `Φ₀` of `X₀`: `Φ ≫ p = p ≫ Φ₀`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberFrobenius_comp_geometricFiberProj`, with `Φ₀`
unfolded). -/
lemma geometricFiberFrobenius_comp_geometricFiberProj_eq_comp_iterateFrobenius :
    f.geometricFiberFrobenius ≫ f.geometricFiberProj =
      f.geometricFiberProj ≫ X₀.iterateFrobenius (FiniteField.ringChar_prime k)
        (Scheme.isOfCharacteristic_of_hom_spec f) (FiniteField.frobeniusExponent k) :=
  Scheme.Hom.geometricFiberFrobenius_comp_geometricFiberProj f

/-- The pullback `p^*` along the projection `p : X̄ ⟶ X₀` of the geometric fibre is invariant
under the scheme Frobenius `Φ = Φ₀ × 𝟙`: `p^* ⋙ Φ^* ≅ (Φ ≫ p)^* = (p ≫ Φ₀)^* ≅ Φ₀^* ⋙ p^* ≅ p^*`,
since `Φ ≫ p = p ≫ Φ₀`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberFrobenius_comp_geometricFiberProj`) and the
pullback along the absolute Frobenius `Φ₀` of `X₀` is trivial
(`AlgebraicGeometry.ProEtale.CondensedRing.upperStarIterateFrobeniusIso`). -/
noncomputable def geometricFiberProjUpperStarModelFrobeniusIso :
    upperStar Λ f.geometricFiberProj ⋙ upperStar Λ f.geometricFiberFrobenius ≅
      upperStar Λ f.geometricFiberProj :=
  ((upperStarComp Λ f.geometricFiberFrobenius f.geometricFiberProj).symm ≪≫
    upperStarCongr Λ (geometricFiberFrobenius_comp_geometricFiberProj_eq_comp_iterateFrobenius f) ≪≫
    upperStarComp Λ f.geometricFiberProj (X₀.iterateFrobenius (FiniteField.ringChar_prime k)
        (Scheme.isOfCharacteristic_of_hom_spec f) (FiniteField.frobeniusExponent k))) ≪≫
    Functor.isoWhiskerRight (upperStarIterateFrobeniusIso Λ (FiniteField.ringChar_prime k)
      (Scheme.isOfCharacteristic_of_hom_spec f) (FiniteField.frobeniusExponent k))
      (upperStar Λ f.geometricFiberProj) ≪≫
    Functor.leftUnitor _

/-- **The two Weil structures on a pulled-back object agree**: the structure isomorphism
`p^* ⋙ Φ^* ≅ p^*` of the scheme Frobenius `Φ`, built from `Φ ≫ p = p ≫ Φ₀` and the
trivialization of the pullback along the absolute Frobenius `Φ₀` of `X₀`, is the
identification `Φ^* ≅ Fr_X^*` of
`AlgebraicGeometry.ProEtale.CondensedRing.upperStarGeometricFiberFrobeniusIso` followed by the
structure isomorphism `p^* ⋙ Fr_X^* ≅ p^*` of the geometric Galois Frobenius `Fr_X`. The key
input is the naturality of the absolute Frobenius trivialization under the pullback `p^*`
(`ProEtale.CondensedRing.upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app`). -/
theorem geometricFiberProjUpperStarModelFrobeniusIso_eq :
    geometricFiberProjUpperStarModelFrobeniusIso Λ f =
      Functor.isoWhiskerLeft _ (upperStarGeometricFiberFrobeniusIso Λ f) ≪≫
        geometricFiberProjUpperStarFrobeniusIso Λ f :=
  upperStarComp_symm_trans_isoWhiskerRight_eq_isoWhiskerLeft_trans Λ f.geometricFiberProj
    (f.geometricFiber.iterateFrobenius (FiniteField.ringChar_prime k)
      f.isOfCharacteristic_geometricFiber (FiniteField.frobeniusExponent k))
    f.geometricGaloisFrobenius.asIso.hom f.geometricFiberFrobenius
    (X₀.iterateFrobenius (FiniteField.ringChar_prime k) (Scheme.isOfCharacteristic_of_hom_spec f)
      (FiniteField.frobeniusExponent k))
    (upperStarIterateFrobeniusIso Λ (FiniteField.ringChar_prime k)
      f.isOfCharacteristic_geometricFiber (FiniteField.frobeniusExponent k))
    (upperStarIterateFrobeniusIso Λ (FiniteField.ringChar_prime k)
      (Scheme.isOfCharacteristic_of_hom_spec f) (FiniteField.frobeniusExponent k))
    (Scheme.Hom.geometricFiberFrobenius_eq_iterateFrobenius_comp f).symm
    (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj f)
    (geometricFiberFrobenius_comp_geometricFiberProj_eq_comp_iterateFrobenius f)
    (Scheme.comp_iterateFrobenius (FiniteField.ringChar_prime k) f.geometricFiberProj
      (Scheme.isOfCharacteristic_of_hom_spec f) f.isOfCharacteristic_geometricFiber
      (FiniteField.frobeniusExponent k))
    fun M ↦ by
      rw [upperStarCongr_hom_app]
      exact upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app Λ
        (FiniteField.ringChar_prime k) (Scheme.isOfCharacteristic_of_hom_spec f)
        f.isOfCharacteristic_geometricFiber (FiniteField.frobeniusExponent k)
        f.geometricFiberProj M

/-- The Weil structure of a pulled-back object for the scheme Frobenius: a module object `M`
over `Λ` on the model `X₀` gives the Weil object `p^* M` on the geometric fibre for the scheme
Frobenius `Φ = Φ₀ × 𝟙`, with structure isomorphism
`Φ^* p^* M ≅ (Φ ≫ p)^* M = (p ≫ Φ₀)^* M ≅ p^* Φ₀^* M ≅ p^* M`
(`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberProjUpperStarModelFrobeniusIso`). -/
noncomputable def geometricFiberWeilModelFrobenius :
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀) ⥤
      Endofunctor.IsoAlgebra (upperStar Λ f.geometricFiberFrobenius) :=
  Endofunctor.IsoAlgebra.functorOfNatIso _ (geometricFiberProjUpperStarModelFrobeniusIso Λ f)

/-- The Weil objects of the scheme Frobenius composed with the forgetful functor are the pullback
along the projection `p : X̄ ⟶ X₀`. -/
lemma geometricFiberWeilModelFrobenius_comp_forget :
    geometricFiberWeilModelFrobenius Λ f ⋙ Endofunctor.IsoAlgebra.forget _ =
      upperStar Λ f.geometricFiberProj :=
  rfl

/-- The transport of Weil objects for the geometric Galois Frobenius `Fr_X` to Weil objects for
the scheme Frobenius `Φ` of the geometric fibre, along the identification `Φ^* ≅ Fr_X^*`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperStarGeometricFiberFrobeniusIso`): a Weil object
`(K, Fr_X^* K ≅ K)` becomes `(K, Φ^* K ≅ Fr_X^* K ≅ K)`. -/
noncomputable def geometricFiberFrobeniusTransport :
    Endofunctor.IsoAlgebra (upperStar Λ f.geometricGaloisFrobenius.asIso.hom) ⥤
      Endofunctor.IsoAlgebra (upperStar Λ f.geometricFiberFrobenius) :=
  Endofunctor.IsoAlgebra.mapOfNatIso (Functor.leftUnitor _ ≪≫
    upperStarGeometricFiberFrobeniusIso Λ f ≪≫ (Functor.rightUnitor _).symm)

instance : (geometricFiberFrobeniusTransport Λ f).IsEquivalence :=
  Endofunctor.IsoAlgebra.isEquivalence_mapOfNatIso _

/-- **The two Weil structures on pulled-back objects agree**, as an isomorphism of functors with
identity underlying morphisms: the transport along `Φ^* ≅ Fr_X^*` of the Weil objects `p^* M` for
the geometric Galois Frobenius `Fr_X`
(`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeil`) are the Weil objects `p^* M` for
the scheme Frobenius `Φ`
(`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilModelFrobenius`). -/
noncomputable def geometricFiberWeilCompTransportIso :
    geometricFiberWeil Λ f ⋙ geometricFiberFrobeniusTransport Λ f ≅
      geometricFiberWeilModelFrobenius Λ f :=
  Endofunctor.IsoAlgebra.functorOfNatIsoCompMapOfNatIsoIso (upperStar Λ f.geometricFiberProj)
    (upperStarGeometricFiberFrobeniusIso Λ f) (geometricFiberProjUpperStarFrobeniusIso Λ f)
    (geometricFiberProjUpperStarModelFrobeniusIso Λ f)
    (geometricFiberProjUpperStarModelFrobeniusIso_eq Λ f)

/-- The components of `AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilCompTransportIso`
have identity underlying morphisms. -/
@[simp]
lemma geometricFiberWeilCompTransportIso_hom_app_hom_f
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X₀) Ab.{u + 1})
      (condensedRingObj Λ X₀)) :
    ((geometricFiberWeilCompTransportIso Λ f).hom.app M).hom.f =
      𝟙 ((upperStar Λ f.geometricFiberProj).obj M) :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
