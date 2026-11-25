/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
public import
    WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobeniusNaturality
public import WeilConjectures.WeilObject.Sheaf.StalkFrobenius
public import WeilConjectures.TraceFormula.BaseChange.Basic
public import WeilConjectures.TraceFormula.Stalk
public import WeilConjectures.TraceFormula.BaseChange.Coherence

/-!

# The base change of Weil objects from a finite field to an algebraically closed field

Let `ℓ` be a prime, `k = 𝔽_q` a finite field of characteristic `p ≠ ℓ`, `Ω` a separably closed
field containing `k` (in the applications the algebraic closure `k̄`), `X` a separated scheme of
finite type over `Spec k` and `π : X̄ = X ×_k Ω ⟶ X` its base change
(`WeilConjectures.TraceFormula.BaseChange.Basic`). A Weil object `(K, φ)` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for
an endomorphism `g` of `X` over `Spec k` gives a Weil object `(Lπ^* K, φ̄)` of `Dᵇc(X̄)⟦ℚ̲̄_ℓ⟧`
for the model Frobenius `Φ = (g ≫ F_X^N) ×_k Ω` (`baseChangeModelFrobenius`), with
`N = n + 1` (`ProEtale.CondensedRing.weilGeometricBaseChange`). Its structure isomorphism is
```
LΦ^* Lπ^* K ≅ L(Φ ≫ π)^* K = L(π ≫ g ≫ F_X^N)^* K ≅ Lπ^* Lg^* LF_X^{N*} K
  --Lκ--> Lπ^* Lg^* K --Lπ^* φ--> Lπ^* K,
```
where `κ : (F_X^N)^* ≅ 𝟭` is the trivialization of the pullback along the `q^N`-power Frobenius
(`ProEtale.CondensedRing.upperStarFrobeniusIso`). For an automorphism `e` of `X` and
`g = e^{n+1}`, this is the bridge between the Weil objects of
`WeilConjectures.TraceFormula.Statement`, over `k` with the Frobenius `σ^{n+1}` twisted by
`e^{n+1}`, and the model-Frobenius setting of the Lefschetz–Verdier formula over `k̄`.

## The Frobenius trivialization

The absolute Frobenius of a scheme of characteristic `p` acts trivially on its pro-étale topos:
the relative Frobenius of a weakly étale `V ⟶ X` is an isomorphism, so the base change along the
absolute Frobenius is isomorphic to the identity on the pro-étale site (blueprint
`lemma-scheme-frobenius-geometric-frobenius--1`, `ProEtale.upperStarIterateFrobeniusIso`). Writing
`#k = p ^ a`, the Frobenius `F_X^N` is the absolute `p ^ (a N)`-power Frobenius. Its
trivialization on abelian sheaves is monoidal and fixes the coefficient ring `Λ_X`, which is
pulled back from the point, so it gives `κ : (F_X^N)^* ≅ 𝟭` on `ℚ̲̄_ℓ`-modules
(`ProEtale.CondensedRing.upperStarFrobeniusIso`). At a
geometric point `ȳ : Spec Ω ⟶ X`, the trivialization `κ` restricts to the trivialization
`(σ)^* ≅ 𝟭` of the pullback along the automorphism `σ` of `Spec Ω` inverse to the
`q^N`-power Frobenius of `Spec Ω` (`upperStarIsoIdOfIsSepClosed`), since `(σ ≫ ȳ) ≫ F_X^N = ȳ`
(`ProEtale.CondensedRing.isGaloisCompatibleFrobeniusIso_upperStarFrobeniusIso`). It follows from the
naturality of `κ` under pullback
    (`upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app`)
and from the fact that on `Spec Ω` the Frobenius and Galois trivializations are inverse
(`upperStarIterateFrobeniusIso_comp_upperStarIsoIdOfIsSepClosed`), both being the identity on the
modules pulled back from the condensed point.

## Main definitions

- `ProEtale.CondensedRing.upperStarFrobeniusIso`: the trivialization `(F_X^N)^* ≅ 𝟭`, and its
  derived version `ProEtale.CondensedRing.leftDerivedUpperStarFrobeniusIso`.
- `ProEtale.CondensedRing.geometricBaseChangeUpperStar`: the derived pullback
  `Lπ^* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X̄)⟦ℚ̲̄_ℓ⟧` along the base change.
- `ProEtale.CondensedRing.weilGeometricBaseChange`: the base change of Weil objects
  `WeilBoundedConstructible ℓ g ⥤ WeilBoundedConstructible ℓ (baseChangeModelFrobenius Ω X (n + 1)
      g)`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Iso

variable {C E : Type*} [Category C] [Category E] {A C' : C ⥤ E} {B : C ⥤ C}

/-- The isomorphism `A ≅ C'` obtained from `A ≅ B ⋙ C'` and a trivialization `B ≅ 𝟭`. -/
def compIsoOfIsoId (c : A ≅ B ⋙ C') (κ : B ≅ 𝟭 C) : A ≅ C' :=
  c ≪≫ Functor.isoWhiskerRight κ C' ≪≫ C'.leftUnitor

/-- The components of `compIsoOfIsoId c κ` are the composites
```
A M --c--> C' (B M) --C' κ_M--> C' M.
```
-/
lemma compIsoOfIsoId_hom_app (c : A ≅ B ⋙ C') (κ : B ≅ 𝟭 C) (M : C) :
    (compIsoOfIsoId c κ).hom.app M = c.hom.app M ≫ C'.map (κ.hom.app M) := by
  simp [compIsoOfIsoId]

end CategoryTheory.Iso

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] [Finite k] {Ω : Type u} [Field Ω] [Algebra k Ω]

omit [Algebra k Ω] in
/-- Let `σ` be an automorphism of `Spec Ω` whose inverse is `Spec(y ↦ y ^ (#k ^ N))`. A morphism
`ȳ : Spec Ω ⟶ X` satisfies `(σ ≫ ȳ) ≫ F_X^N = ȳ`: the `#k ^ N`-power Frobenius `F_X^N` acts on
`σ ≫ ȳ` through the `#k ^ N`-power map of `Ω`. -/
lemma comp_comp_frobeniusIterate_overFrobenius_left [Algebra k Ω] {X : Over (Spec (.of k))}
    {N : ℕ} {σ : Spec (.of Ω) ≅ Spec (.of Ω)} (hσ : σ.inv = Spec.map (powCardPowRingHom k Ω N))
    (y : Spec (.of Ω) ⟶ X.left) :
    (σ.hom ≫ y) ≫ (frobeniusIterate (overFrobenius X) N).left = y := by
  rw [isFrobenius_frobeniusIterate_overFrobenius_left X N _ _ (powCardPowRingHom_apply N), ← hσ,
    Iso.inv_hom_id_assoc]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The Frobenius trivialization -/

section Frobenius

variable (X : Over (Spec (.of k))) (N : ℕ)

/-- The compatibility at a geometric point `ȳ : Spec Ω ⟶ X` of a trivialization `κ : F^* ≅ 𝟭` of
the pullback along the `#k ^ N`-power Frobenius `F` with a trivialization `τ : σ^* ≅ 𝟭` of the
pullback along the automorphism `σ` of `Spec Ω` inverse to the `#k ^ N`-power Frobenius: writing
`ȳ = (σ ≫ ȳ) ≫ F`, the two identifications `ȳ^* M ≅ σ^* ȳ^* M ≅ (σ ≫ ȳ)^* M` and
`ȳ^* M = ((σ ≫ ȳ) ≫ F)^* M ≅ (σ ≫ ȳ)^* F^* M --κ--> (σ ≫ ȳ)^* M` agree. -/
def IsGaloisCompatibleFrobeniusIsoAt
    (κ : ((frobeniusIterate (overFrobenius X) N).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _)
    {Ω : Type u} [Field Ω] [Algebra k Ω] (σ : Spec (.of Ω) ≅ Spec (.of Ω))
    (hσ : σ.inv = Spec.map (powCardPowRingHom k Ω N)) (y : Spec (.of Ω) ⟶ X.left)
    (τ : (σ.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _) : Prop :=
  ∀ M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left),
    τ.inv.app ((y)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ.hom y).inv.app M =
      eqToHom (congrArg (fun t : Spec (.of Ω) ⟶ X.left ↦
          (t)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M)
          (comp_comp_frobeniusIterate_overFrobenius_left hσ y).symm) ≫
        (upperStarComp (Profinite.padicAlgClRingObj ℓ) (σ.hom ≫ y)
          (frobeniusIterate (overFrobenius X) N).left).hom.app M ≫
        (σ.hom ≫ y)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map (κ.hom.app M)

/-- **Galois compatibility of a trivialization of the Frobenius pullback** (blueprint
`lemma-scheme-frobenius-geometric-frobenius--1`, with its comparison with the Galois pullbacks at
geometric points, blueprint `lemma-scheme-frobenius-geometric-frobenius--1`). Let `X` be a scheme
over the finite field `k` and `F = F_X^N` its `#k ^ N`-power Frobenius. The pullback `F^*` on
`ℚ̲̄_ℓ`-modules on the pro-étale site of `X` has a trivialization `κ : F^* ≅ 𝟭`: the relative
Frobenius of a weakly étale `V ⟶ X` is a weakly étale universal homeomorphism, hence an isomorphism,
so the base change along `F` is isomorphic to the identity on the pro-étale site.

At a geometric point the canonical trivialization is the trivialization of a Galois pullback:
let `Ω ⊇ k` be separably closed, `σ` the automorphism of `Spec Ω` inverse to the
`#k ^ N`-power Frobenius `F_Ω = Spec(y ↦ y ^ (#k ^ N))` (for `Ω = k̄`, the `N`-th power of the
Galois Frobenius) and `ȳ : Spec Ω ⟶ X`. Writing `ȳ = (σ ≫ ȳ) ≫ F`
(`comp_comp_frobeniusIterate_overFrobenius_left`), the two identifications
```
ȳ^* M ≅ σ^* ȳ^* M ≅ (σ ≫ ȳ)^* M,
ȳ^* M = ((σ ≫ ȳ) ≫ F)^* M ≅ (σ ≫ ȳ)^* F^* M --κ--> (σ ≫ ȳ)^* M
```
agree, the first one through the trivialization `τ : σ^* ≅ 𝟭` of `upperStarIsoIdOfIsSepClosed`.
Indeed `κ` is compatible with pullbacks along morphisms of schemes of characteristic `p`, and on
`Spec Ω` the trivialization `κ` of `F_Ω^*` is the inverse of `τ` composed with the identity
`(F_Ω ≫ σ)^* = 𝟙^*`: both are the identity on the sheaves pulled back from the condensed point,
which are all sheaves on `Spec Ω`. -/
def IsGaloisCompatibleFrobeniusIso
    (κ : ((frobeniusIterate (overFrobenius X) N).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _) :
    Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra k Ω] (σ : Spec (.of Ω) ≅ Spec (.of Ω))
    (hσ : σ.inv = Spec.map (powCardPowRingHom k Ω N)) (y : Spec (.of Ω) ⟶ X.left),
    IsGaloisCompatibleFrobeniusIsoAt ℓ X N κ σ hσ y
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom)

/-- **The trivialization of the Frobenius pullback** (blueprint
`lemma-scheme-frobenius-geometric-frobenius--1`): the pullback along the `#k ^ N`-power Frobenius
`F = F_X^N` on `ℚ̲̄_ℓ`-modules on the pro-étale site of `X` is trivialized by the relative Frobenius
isomorphisms. Writing `#k = p ^ a`, the Frobenius `F` is the absolute `p ^ (a N)`-power Frobenius
(`frobeniusIterate_overFrobenius_left`), whose pullback of abelian sheaves has the monoidal
trivialization `ProEtale.upperStarIterateFrobeniusIso`; it fixes the coefficient ring `Λ_X`, which
is pulled back from the point (`ProEtale.upperStarIterateFrobeniusIso_hom_app_upperStarFromPoint`),
so it induces a trivialization on `Λ_X`-modules (`upperStarIterateFrobeniusIso`). -/
noncomputable def upperStarFrobeniusIso :
    ((frobeniusIterate (overFrobenius X) N).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _ :=
  upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) (frobeniusIterate_overFrobenius_left X N) ≪≫
    upperStarIterateFrobeniusIso (Profinite.padicAlgClRingObj ℓ)
      (FiniteField.ringChar_prime (k := k))
      (natCast_ringChar_left_eq_zero X) (FiniteField.frobeniusExponent k * N)

lemma upperStarFrobeniusIso_eq :
    upperStarFrobeniusIso ℓ X N =
      upperStarEqToIso (Profinite.padicAlgClRingObj ℓ) (frobeniusIterate_overFrobenius_left X N) ≪≫
        upperStarIterateFrobeniusIso (Profinite.padicAlgClRingObj ℓ)
          (FiniteField.ringChar_prime (k := k))
          (natCast_ringChar_left_eq_zero X) (FiniteField.frobeniusExponent k * N) :=
  rfl

/-- The components of `upperStarEqToIso h ≪≫ κ`. -/
lemma upperStarEqToIso_trans_hom_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {A : Scheme.{u}} {t t' : A ⟶ A} (h : t = t') (κ : (t')^*⟦Λ⟧ ≅ 𝟭 _) (M) :
    (upperStarEqToIso Λ h ≪≫ κ).hom.app M =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj M) h) ≫ κ.hom.app M := by
  rw [Iso.trans_hom, NatTrans.comp_app, upperStarEqToIso_hom_app]

/-- The trivialization `Lκ : L(F_X^N)^* ≅ 𝟭` of the derived pullback along the `#k ^ N`-power
Frobenius: the derived functor of `upperStarFrobeniusIso`. -/
noncomputable def leftDerivedUpperStarFrobeniusIso :
    L(((frobeniusIterate (overFrobenius X) N).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ≅ 𝟭 _ :=
  Functor.leftDerivedFunctorIdIso (upperStarFrobeniusIso ℓ X N)

/-- The transport of the pullback of module objects along an equality of morphisms is
`upperStarEqToIso`. -/
lemma upperStarCongr_eq_upperStarEqToIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {A B : Scheme.{u}} {t t' : A ⟶ B} (h : t = t') :
    upperStarCongr Λ h = upperStarEqToIso Λ h := by
  subst h
  ext M
  rw [upperStarEqToIso_hom_app]
  simp [upperStarCongr]

/-- The associativity law of the composition isomorphisms of the pullbacks of module objects, with
the transport written through `eqToHom` of objects. -/
lemma upperStarComp_assoc_app_eqToHom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {W' X' Y' Z' : Scheme.{u}} (f : W' ⟶ X') (g : X' ⟶ Y') (h : Y' ⟶ Z') (M) :
    (upperStarComp Λ (f ≫ g) h).hom.app M ≫ (upperStarComp Λ f g).hom.app ((h)^*⟦Λ⟧.obj M) =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj M) (Category.assoc f g h)) ≫
        (upperStarComp Λ f (g ≫ h)).hom.app M ≫
          (f)^*⟦Λ⟧.map ((upperStarComp Λ g h).hom.app M) := by
  rw [upperStarComp_hom_app_comp_upperStarComp_hom_app, upperStarCongr_eq_upperStarEqToIso,
    upperStarEqToIso_hom_app]


/-! ### The Galois compatibility of the Frobenius trivialization -/

section GaloisCompatibility

/-- The components of `α ≫ ρ_G⁻¹ ≫ G ◁ κ`, for `κ : 𝟭 ⟶ F`. -/
lemma _root_.CategoryTheory.NatTrans.comp_rightUnitor_inv_comp_whiskerLeft_app {C D : Type*}
    [Category C] [Category D] {F : D ⥤ D} {G H : C ⥤ D} (α : H ⟶ G) (κ : 𝟭 D ⟶ F) (c : C) :
    (α ≫ (Functor.rightUnitor G).inv ≫ Functor.whiskerLeft G κ).app c =
      α.app c ≫ κ.app (G.obj c) := by
  simp

/-- The left unit law for the composition isomorphisms of the pullbacks of module objects, on
components: `(𝟙 ≫ t)^* M = t^* M ≅ 𝟙^* t^* M`. -/
lemma upperStarComp_id_left_hom_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {A B : Scheme.{u}} (t : A ⟶ B) (M) :
    (upperStarComp Λ (𝟙 A) t).hom.app M =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj M) (Category.id_comp t)) ≫
        (upperStarId Λ A).inv.app ((t)^*⟦Λ⟧.obj M) := by
  have h := congrArg (fun i ↦ i.hom.app M) (upperStarComp_id_left Λ t)
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom] at h
  rw [NatTrans.comp_rightUnitor_inv_comp_whiskerLeft_app, upperStarCongr_hom_app] at h
  exact h

/-- The Galois compatibility of the Frobenius trivialization at a geometric point, for the
`p ^ m`-power absolute Frobenius of a scheme `X` of characteristic `p` and an endomorphism `σ` of
`Spec Ω` with `F_Ω ≫ σ = 𝟙`. -/
theorem upperStarIsoIdOfIsSepClosed_inv_app_comp_upperStarComp_inv_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (m : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (hΩ : (p : Γ(Spec (.of Ω), ⊤)) = 0)
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (hFσ : (Spec (.of Ω)).iterateFrobenius hp hΩ m ≫ σ = 𝟙 _)
    (y : Spec (.of Ω) ⟶ X) (F' : X ⟶ X) (hF' : F' = X.iterateFrobenius hp hX m)
    (e : y = (σ ≫ y) ≫ F') (τ : (σ)^*⟦Λ⟧ ≅ 𝟭 _)
    (hτ : ∀ N, (upperStarId Λ _).inv.app N ≫ eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj N) hFσ.symm) ≫
      (upperStarComp Λ ((Spec (.of Ω)).iterateFrobenius hp hΩ m) σ).hom.app N ≫
      ((Spec (.of Ω)).iterateFrobenius hp hΩ m)^*⟦Λ⟧.map (τ.hom.app N) ≫
      (upperStarIterateFrobeniusIso Λ hp hΩ m).hom.app N = 𝟙 N) (M) :
    τ.inv.app ((y)^*⟦Λ⟧.obj M) ≫
        (upperStarComp Λ σ y).inv.app M =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj M) e) ≫ (upperStarComp Λ (σ ≫ y) F').hom.app M ≫
        (σ ≫ y)^*⟦Λ⟧.map (eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj M) hF') ≫
          (upperStarIterateFrobeniusIso Λ hp hX m).hom.app M) :=
  inv_app_comp_inv_app_eq_aux
    (E := fun S ↦ Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (fun a ↦ (a)^*⟦Λ⟧) (fun a b ↦ upperStarComp Λ a b)
    (fun a b c M ↦ upperStarComp_assoc_app_eqToHom Λ a b c M) (fun A ↦ upperStarId Λ A)
    (fun t M ↦ upperStarComp_id_left_hom_app Λ t M) y σ _ _ F' hF' hFσ
    (comp_iterateFrobenius hp (σ ≫ y) hX hΩ m) e (upperStarIterateFrobeniusIso Λ hp hX m)
    (upperStarIterateFrobeniusIso Λ hp hΩ m) τ
    (fun M ↦ upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app Λ hp hX hΩ m
      (σ ≫ y) M)
    hτ M

/-- The Galois compatibility at a geometric point `ȳ` of the Frobenius trivialization, for any
trivialization `τ : σ^* ≅ 𝟭` inverse to the Frobenius trivialization of `Spec Ω` through
`F_Ω ≫ σ = 𝟙`. -/
lemma isGaloisCompatibleFrobeniusIsoAt_of {Ω : Type u} [Field Ω] [IsSepClosed Ω] [Algebra k Ω]
    (σ : Spec (.of Ω) ≅ Spec (.of Ω)) (hσ : σ.inv = Spec.map (powCardPowRingHom k Ω N))
    (y : Spec (.of Ω) ⟶ X.left) (hΩ : (ringChar k : Γ(Spec (.of Ω), ⊤)) = 0)
    (hFσ : (Spec (.of Ω)).iterateFrobenius (FiniteField.ringChar_prime (k := k)) hΩ
      (FiniteField.frobeniusExponent k * N) ≫ σ.hom = 𝟙 _)
    (τ : (σ.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _)
    (hτ : τ = upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ.hom) :
    IsGaloisCompatibleFrobeniusIsoAt ℓ X N (upperStarFrobeniusIso ℓ X N) σ hσ y τ := by
  intro M
  have key := upperStarIsoIdOfIsSepClosed_inv_app_comp_upperStarComp_inv_app
    (Profinite.padicAlgClRingObj ℓ) (FiniteField.ringChar_prime (k := k))
    (natCast_ringChar_left_eq_zero X) (FiniteField.frobeniusExponent k * N) hΩ σ.hom hFσ y
    _ (frobeniusIterate_overFrobenius_left X N)
    (comp_comp_frobeniusIterate_overFrobenius_left hσ y).symm τ
    (fun N' ↦ upperStarIterateFrobeniusIso_comp_eq_id_of_eq _
      (FiniteField.ringChar_prime (k := k)) hΩ _
      σ.hom hFσ τ hτ N') M
  have hκ : (upperStarFrobeniusIso ℓ X N).hom.app M =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M)
        (frobeniusIterate_overFrobenius_left X N)) ≫
        (upperStarIterateFrobeniusIso (Profinite.padicAlgClRingObj ℓ)
          (FiniteField.ringChar_prime (k := k)) (natCast_ringChar_left_eq_zero X)
          (FiniteField.frobeniusExponent k * N)).hom.app M := by
    rw [upperStarFrobeniusIso_eq, upperStarEqToIso_trans_hom_app]
  rw [hκ]
  exact key

/-- **The Galois compatibility of the Frobenius trivialization** (`IsGaloisCompatibleFrobeniusIso`):
at a geometric point `ȳ : Spec Ω ⟶ X`, the trivialization `κ : (F_X^N)^* ≅ 𝟭` of the pullback
along the `#k ^ N`-power Frobenius restricts to the trivialization `τ : σ^* ≅ 𝟭` of the pullback
along the automorphism `σ` of `Spec Ω` inverse to the `#k ^ N`-power Frobenius `F_Ω`. It follows
from the naturality of the Frobenius trivialization along `σ ≫ ȳ`
(`upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app`) and from the fact that
on `Spec Ω` the trivializations `κ_Ω : F_Ω^* ≅ 𝟭` and `τ` are inverse through `F_Ω ≫ σ = 𝟙`
(`upperStarIterateFrobeniusIso_comp_upperStarIsoIdOfIsSepClosed`), by the coherence of the
composition isomorphisms (`inv_app_comp_inv_app_eq_aux`). -/
theorem isGaloisCompatibleFrobeniusIso_upperStarFrobeniusIso :
    IsGaloisCompatibleFrobeniusIso ℓ X N (upperStarFrobeniusIso ℓ X N) := by
  intro Ω' _ _ _ σ hσ y
  have hΩ : (ringChar k : Γ(Spec (.of Ω'), ⊤)) = 0 :=
    Scheme.isOfCharacteristic_Spec (ringChar_cast_eq_zero (k := k) (Ω := Ω'))
  have hFσ : (Spec (.of Ω')).iterateFrobenius (FiniteField.ringChar_prime (k := k)) hΩ
      (FiniteField.frobeniusExponent k * N) ≫ σ.hom = 𝟙 _ := by
    rw [iterateFrobenius_spec_eq_specMap_powCardPowRingHom, ← hσ, Iso.inv_hom_id]
  exact isGaloisCompatibleFrobeniusIsoAt_of ℓ X N σ hσ y hΩ hFσ _ rfl


end GaloisCompatibility

end Frobenius

/-! ### The pullback along the base change -/

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

section UpperStar

set_option linter.unusedSectionVars false in
/-- The derived pullback along the base change `π : X̄ ⟶ X` preserves bounded constructible
complexes (blueprint `proposition-six-operations-dctf`, with the pullback of constructible sheaves
`prop-constructible-pullback`): `Lπ^*` is computed levelwise by the exact functor `π^*`, so it
commutes with the homology sheaves, and the pullback of a sheaf which is constructible along a
finite stratification of `X` by locally closed constructible strata is constructible along the
preimage stratification of `X̄`
(`ProEtale.CondensedRing.boundedConstructible_leftDerivedUpperStar_obj_of_scheme`). -/
theorem boundedConstructible_leftDerivedUpperStar_geometricBaseChangeProj_obj
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) K) :
    boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) ((geometricBaseChange k Ω).obj X).left)
      ((L((geometricBaseChangeProj (Ω := Ω) X)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K) :=
  boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ K hK

variable (Ω) in
/-- The derived pullback `Lπ^* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X̄)⟦ℚ̲̄_ℓ⟧` along the base change
`π : X̄ ⟶ X`: the restriction of `L((π)^*⟦ℚ̲̄_ℓ⟧)`. -/
noncomputable def geometricBaseChangeUpperStar :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(((geometricBaseChange k Ω).obj X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
      L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
    fun K ↦ boundedConstructible_leftDerivedUpperStar_geometricBaseChangeProj_obj ℓ X K.obj
      K.property

@[simp]
lemma geometricBaseChangeUpperStar_obj_obj (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((geometricBaseChangeUpperStar Ω ℓ X).obj K).obj =
      L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj :=
  rfl

@[simp]
lemma geometricBaseChangeUpperStar_map_hom {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : K ⟶ K') :
    ((geometricBaseChangeUpperStar Ω ℓ X).map φ).hom =
      L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map φ.hom :=
  rfl

end UpperStar

/-! ### The base change of Weil objects -/

section Weil

variable (N : ℕ) (g : X ⟶ X)

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The model Frobenius `Φ = (g ≫ F_X^N) ×_k Ω` lies over `g ≫ F_X^N`. -/
lemma modelFrobenius_left_comp_proj' :
    (baseChangeModelFrobenius Ω X N g).left ≫ geometricBaseChangeProj X =
      geometricBaseChangeProj X ≫ g.left ≫ (frobeniusIterate (overFrobenius X) N).left :=
  modelFrobenius_left_comp_proj X N g

variable (Ω) in
/-- The Frobenius comparison of the base change on the ambient derived categories:
`L(Φ ≫ π)^* ≅ Lπ^* Lg^*`, the composite
```
L(Φ ≫ π)^* = L(π ≫ g ≫ F)^* ≅ Lπ^* L(g ≫ F)^* ≅ Lπ^* Lg^* LF^* --Lκ--> Lπ^* Lg^*
```
for `F = F_X^N`. -/
noncomputable def leftDerivedUpperStarModelFrobeniusIso :
    L(((baseChangeModelFrobenius Ω X N g).left ≫ geometricBaseChangeProj X)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧) ≅
      L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  pullbackCongrIso (D := fun S ↦ DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) S)))
      (fun t ↦ L((t)^*⟦Profinite.padicAlgClRingObj ℓ⟧))
      (modelFrobenius_left_comp_proj' X N g) ≪≫
    leftDerivedUpperStarComp _ (geometricBaseChangeProj X)
      (g.left ≫ (frobeniusIterate (overFrobenius X) N).left) ≪≫
    Functor.isoWhiskerRight (Iso.compIsoOfIsoId
      (leftDerivedUpperStarComp _ g.left (frobeniusIterate (overFrobenius X) N).left)
      (leftDerivedUpperStarFrobeniusIso ℓ X N)) _

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The components of `leftDerivedUpperStarModelFrobeniusIso`. -/
lemma leftDerivedUpperStarModelFrobeniusIso_hom_app
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))) :
    (leftDerivedUpperStarModelFrobeniusIso Ω ℓ X N g).hom.app M =
      eqToHom (congrArg (fun t : ((geometricBaseChange k Ω).obj X).left ⟶ X.left ↦
          L((t)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj M) (modelFrobenius_left_comp_proj' X N g)) ≫
        (leftDerivedUpperStarComp _ (geometricBaseChangeProj X)
          (g.left ≫ (frobeniusIterate (overFrobenius X) N).left)).hom.app M ≫
        L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          ((leftDerivedUpperStarComp _ g.left (frobeniusIterate (overFrobenius X) N).left).hom.app
              M ≫
            L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
              ((leftDerivedUpperStarFrobeniusIso ℓ X N).hom.app M)) := by
  simp only [leftDerivedUpperStarModelFrobeniusIso, Iso.trans_hom, NatTrans.comp_app,
    pullbackCongrIso_hom_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.compIsoOfIsoId_hom_app]

variable (Ω) in
/-- The Frobenius comparison `Lπ^* ⋙ LΦ^* ≅ Lg^* ⋙ Lπ^*` of the base change on the ambient
derived categories: `(leftDerivedUpperStarComp Φ π)⁻¹ ≫ leftDerivedUpperStarModelFrobeniusIso`. -/
noncomputable def leftDerivedUpperStarModelFrobeniusComparison :
    L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L(((baseChangeModelFrobenius Ω X N g).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ≅
      L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L((geometricBaseChangeProj X)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  (leftDerivedUpperStarComp _ (baseChangeModelFrobenius Ω X N g).left (geometricBaseChangeProj
      X)).symm ≪≫
    leftDerivedUpperStarModelFrobeniusIso Ω ℓ X N g

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
lemma leftDerivedUpperStarModelFrobeniusComparison_hom_app
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))) :
    (leftDerivedUpperStarModelFrobeniusComparison Ω ℓ X N g).hom.app K =
      (leftDerivedUpperStarComp _ (baseChangeModelFrobenius Ω X N g).left
          (geometricBaseChangeProj X)).inv.app K ≫
        (leftDerivedUpperStarModelFrobeniusIso Ω ℓ X N g).hom.app K :=
  rfl

variable (Ω) in
/-- The Frobenius comparison `b : Lπ^* ⋙ LΦ^* ≅ Lg^* ⋙ Lπ^*` of the base change on bounded
constructible complexes, for the model Frobenius `Φ = (g ≫ F_X^N) ×_k Ω`: the restriction of
`(leftDerivedUpperStarComp Φ π)⁻¹ ≫ leftDerivedUpperStarModelFrobeniusIso`. -/
noncomputable def weilGeometricBaseChangeComparison :
    geometricBaseChangeUpperStar Ω ℓ X ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (baseChangeModelFrobenius
            Ω X N g) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ⋙
        geometricBaseChangeUpperStar Ω ℓ X :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      ((leftDerivedUpperStarModelFrobeniusComparison Ω ℓ X N g).app K.obj))
    (fun φ ↦ ObjectProperty.hom_ext _
      ((leftDerivedUpperStarModelFrobeniusComparison Ω ℓ X N g).hom.naturality φ.hom))

/-- The components of the Frobenius comparison of the base change. -/
lemma weilGeometricBaseChangeComparison_hom_app
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilGeometricBaseChangeComparison Ω ℓ X N g).hom.app K =
      (ObjectProperty.isoMk _
        ((leftDerivedUpperStarModelFrobeniusComparison Ω ℓ X N g).app K.obj)).hom :=
  rfl

/-- On the ambient derived category, the Frobenius comparison of the base change is
`(leftDerivedUpperStarComp Φ π)⁻¹ ≫ leftDerivedUpperStarModelFrobeniusIso`. -/
lemma weilGeometricBaseChangeComparison_hom_app_hom
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((weilGeometricBaseChangeComparison Ω ℓ X N g).hom.app K).hom =
      (leftDerivedUpperStarModelFrobeniusComparison Ω ℓ X N g).hom.app K.obj :=
  (congrArg InducedCategory.Hom.hom
    (weilGeometricBaseChangeComparison_hom_app (Ω := Ω) ℓ X N g K)).trans
    ((congrArg InducedCategory.Hom.hom (ObjectProperty.isoMk_hom _ _)).trans
      ((ObjectProperty.homMk_hom _).trans (Iso.app_hom _ _)))

variable (Ω) in
/-- **The base change of Weil objects** from `k` to `Ω`: a Weil object `(K, φ)` of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for an endomorphism `g` of `X` over `Spec k` is sent to the Weil object
`(Lπ^* K, φ̄)` of `Dᵇc(X̄)⟦ℚ̲̄_ℓ⟧` for the model Frobenius `Φ = (g ≫ F_X^N) ×_k Ω`, with
```
φ̄ : LΦ^* Lπ^* K --b--> Lπ^* Lg^* K --Lπ^* φ--> Lπ^* K
```
(`weilGeometricBaseChangeComparison`). For `g = 𝟙` and `Ω` algebraically closed, the model
Frobenius is the base change of the `q^N`-power Frobenius
(`exists_isModelFrobenius_modelFrobenius_id`). -/
noncomputable def weilGeometricBaseChange :
    WeilBoundedConstructible ℓ g ⥤ WeilBoundedConstructible ℓ (baseChangeModelFrobenius Ω X N g) :=
  IsoAlgebra.mapOfNatIso (weilGeometricBaseChangeComparison Ω ℓ X N g)

@[simp]
lemma weilGeometricBaseChange_obj_carrier (K : WeilBoundedConstructible ℓ g) :
    ((weilGeometricBaseChange Ω ℓ X N g).obj K).carrier =
      (geometricBaseChangeUpperStar Ω ℓ X).obj K.carrier :=
  rfl

lemma weilGeometricBaseChange_obj_str (K : WeilBoundedConstructible ℓ g) :
    ((weilGeometricBaseChange Ω ℓ X N g).obj K).str =
      (weilGeometricBaseChangeComparison Ω ℓ X N g).app K.carrier ≪≫
        (geometricBaseChangeUpperStar Ω ℓ X).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

end Weil

end AlgebraicGeometry.ProEtale.CondensedRing
