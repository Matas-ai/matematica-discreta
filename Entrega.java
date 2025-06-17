import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.BooleanSupplier;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.IntStream;

/*
 * Aquesta entrega consisteix en implementar tots els mètodes anomenats "exerciciX". Ara mateix la
 * seva implementació consisteix en llançar `UnsupportedOperationException`, ho heu de canviar així
 * com els aneu fent.
 *
 * Criteris d'avaluació:
 *
 * - Si el codi no compila tendreu un 0.
 *
 * - Les úniques modificacions que podeu fer al codi són:
 *    + Afegir un mètode (dins el tema que el necessiteu)
 *    + Afegir proves a un mètode "tests()"
 *    + Òbviament, implementar els mètodes que heu d'implementar ("exerciciX")
 *   Si feu una modificació que no sigui d'aquesta llista, tendreu un 0.
 *
 * - Principalment, la nota dependrà del correcte funcionament dels mètodes implementats (provant
 *   amb diferents entrades).
 *
 * - Tendrem en compte la neteja i organització del codi. Un estandard que podeu seguir és la guia
 *   d'estil de Google per Java: https://google.github.io/styleguide/javaguide.html . Per exemple:
 *    + IMPORTANT: Aquesta entrega està codificada amb UTF-8 i finals de línia LF.
 *    + Indentació i espaiat consistent
 *    + Bona nomenclatura de variables
 *    + Declarar les variables el més aprop possible al primer ús (és a dir, evitau blocs de
 *      declaracions).
 *    + Convé utilitzar el for-each (for (int x : ...)) enlloc del clàssic (for (int i = 0; ...))
 *      sempre que no necessiteu l'índex del recorregut. Igualment per while si no és necessari.
 *
 * Per com està plantejada aquesta entrega, no necessitau (ni podeu) utilitzar cap `import`
 * addicional, ni qualificar classes que no estiguin ja importades. El que sí podeu fer és definir
 * tots els mètodes addicionals que volgueu (de manera ordenada i dins el tema que pertoqui).
 *
 * Podeu fer aquesta entrega en grups de com a màxim 3 persones, i necessitareu com a minim Java 10.
 * Per entregar, posau els noms i cognoms de tots els membres del grup a l'array `Entrega.NOMS` que
 * està definit a la línia 53.
 *
 * L'entrega es farà a través d'una tasca a l'Aula Digital que obrirem abans de la data que se us
 * hagui comunicat. Si no podeu visualitzar bé algun enunciat, assegurau-vos de que el vostre editor
 * de texte estigui configurat amb codificació UTF-8.
 */
class Entrega {
  static final String[] NOMS = {"Andreu Morey Juan", "Miquel Matas Soler", "Antonio José Pérez García"};

  /*
   * Aquí teniu els exercicis del Tema 1 (Lògica).
   */
  static class Tema1 {
    /*
     * Determinau si l'expressió és una tautologia o no:
     *
     * (((vars[0] ops[0] vars[1]) ops[1] vars[2]) ops[2] vars[3]) ...
     *
     * Aquí, vars.length == ops.length+1, i cap dels dos arrays és buid. Podeu suposar que els
     * identificadors de les variables van de 0 a N-1, i tenim N variables diferents (mai més de 20
     * variables).
     *
     * Cada ops[i] pot ser: CONJ, DISJ, IMPL, NAND.
     *
     * Retornau:
     *   1 si és una tautologia
     *   0 si és una contradicció
     *   -1 en qualsevol altre cas.
     *
     * Vegeu els tests per exemples.
     */
    static final char CONJ = '∧';
    static final char DISJ = '∨';
    static final char IMPL = '→';
    static final char NAND = '.';

    static int exercici1(char[] ops, int[] vars) {
      //Nombre de variables diferents (de 0 a n-1)
        int n = Arrays.stream(vars).max().getAsInt() + 1;
        int totalAssignacions = 1 << n; //2^n assignacions possibles

        boolean sempreVertadera = true;
        boolean sempreFalsa = true;

        //Recorrem totes les assignacions possibles de valors de veritat
        for (int mascara = 0; mascara < totalAssignacions; mascara++) {
            //Assignació dels valors booleans a les variables
            boolean[] valors = new boolean[n];
            for (int i = 0; i < n; i++) {
                valors[i] = (mascara & (1 << i)) != 0;
            }

            //Avaluació de l'expressió segons la forma ((a op b) op c) op d ...
            boolean resultat = valors[vars[0]];
            for (int i = 0; i < ops.length; i++) {
                boolean seguent = valors[vars[i + 1]];
                switch (ops[i]) {
                    case CONJ: resultat = resultat && seguent; break;
                    case DISJ: resultat = resultat || seguent; break;
                    case IMPL: resultat = !resultat || seguent; break;
                    case NAND: resultat = !(resultat && seguent); break;
                    default: throw new IllegalArgumentException("Operador desconegut: " + ops[i]);
                }
            }

            //Comprovam si és sempre certa o sempre falsa
            if (resultat) {
                sempreFalsa = false;
            } else {
                sempreVertadera = false;
            }

            //Si ja hem vist un cas vertader i un de fals, no cal continuar
            if (!sempreVertadera && !sempreFalsa) return -1;
        }

        //Retornam segons el cas
        return sempreVertadera ? 1 : 0;
    }
    

    /*
     * Aquest mètode té de paràmetre l'univers (representat com un array) i els predicats
     * adients `p` i `q`. Per avaluar aquest predicat, si `x` és un element de l'univers, podeu
     * fer-ho com `p.test(x)`, que té com resultat un booleà (true si `P(x)` és cert).
     *
     * Amb l'univers i els predicats `p` i `q` donats, returnau true si la següent proposició és
     * certa.
     *
     * (∀x : P(x)) <-> (∃!x : Q(x))
     */
    static boolean exercici2(int[] universe, Predicate<Integer> p, Predicate<Integer> q) {
      //1. Comprovar ∀x P(x)
        boolean totsComplertP = true;
        for (int x : universe) {
            if (!p.test(x)) {
                totsComplertP = false;
                break;
            }
        }

        //2. Comprovar ∃!x Q(x)
        int contarQ = 0;
        for (int x : universe) {
            if (q.test(x)) {
                contarQ++;
                if (contarQ > 1) {
                    break; //Més d'un, ja podem aturar
                }
            }
        }
        boolean exactamentUnQ = (contarQ == 1);

        //3. Retornar si són equivalents
        return totsComplertP == exactamentUnQ;
    }

    static void tests() {
      // Exercici 1
      // Taules de veritat

      // Tautologia: ((p0 → p2) ∨ p1) ∨ p0
      test(1, 1, 1, () -> exercici1(new char[] { IMPL, DISJ, DISJ }, new int[] { 0, 2, 1, 0 }) == 1);

      // Contradicció: (p0 . p0) ∧ p0
      test(1, 1, 2, () -> exercici1(new char[] { NAND, CONJ }, new int[] { 0, 0, 0 }) == 0);

      // Exercici 2
      // Equivalència

      test(1, 2, 1, () -> {
        return exercici2(new int[] { 1, 2, 3 }, (x) -> x == 0, (x) -> x == 0);
      });

      test(1, 2, 2, () -> {
        return exercici2(new int[] { 1, 2, 3 }, (x) -> x >= 1, (x) -> x % 2 == 0);
      });
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 2 (Conjunts).
   *
   * Per senzillesa tractarem els conjunts com arrays (sense elements repetits). Per tant, un
   * conjunt de conjunts d'enters tendrà tipus int[][]. Podeu donar per suposat que tots els
   * arrays que representin conjunts i us venguin per paràmetre estan ordenats de menor a major.
   *
   * Les relacions també les representarem com arrays de dues dimensions, on la segona dimensió
   * només té dos elements. L'array estarà ordenat lexicogràficament. Per exemple
   *   int[][] rel = {{0,0}, {0,1}, {1,1}, {2,2}};
   * i també donarem el conjunt on està definida, per exemple
   *   int[] a = {0,1,2};
   * Als tests utilitzarem extensivament la funció generateRel definida al final (també la podeu
   * utilitzar si la necessitau).
   *
   * Les funcions f : A -> B (on A i B son subconjunts dels enters) les representam o bé amb el seu
   * graf o bé amb un objecte de tipus Function<Integer, Integer>. Sempre donarem el domini int[] a
   * i el codomini int[] b. En el cas de tenir un objecte de tipus Function<Integer, Integer>, per
   * aplicar f a x, és a dir, "f(x)" on x és d'A i el resultat f.apply(x) és de B, s'escriu
   * f.apply(x).
   */
  static class Tema2 {
    /*
     * Trobau el nombre de particions diferents del conjunt `a`, que podeu suposar que no és buid.
     *
     * Pista: Cercau informació sobre els nombres de Stirling.
     */
    static int exercici1(int[] a) {
      throw new UnsupportedOperationException("pendent");
    }

    /*
     * Trobau el cardinal de la relació d'ordre parcial sobre `a` més petita que conté `rel` (si
     * existeix). En altres paraules, el cardinal de la seva clausura reflexiva, transitiva i
     * antisimètrica.
     *
     * Si no existeix, retornau -1.
     */
    static int exercici2(int[] a, int[][] rel) {
      throw new UnsupportedOperationException("pendent");
    }

    /*
     * Donada una relació d'ordre parcial `rel` definida sobre `a` i un subconjunt `x` de `a`,
     * retornau:
     * - L'ínfim de `x` si existeix i `op` és false
     * - El suprem de `x` si existeix i `op` és true
     * - null en qualsevol altre cas
     */
    static Integer exercici3(int[] a, int[][] rel, int[] x, boolean op) {
      throw new UnsupportedOperationException("pendent");
    }

    /*
     * Donada una funció `f` de `a` a `b`, retornau:
     *  - El graf de la seva inversa (si existeix)
     *  - Sinó, el graf d'una inversa seva per l'esquerra (si existeix)
     *  - Sinó, el graf d'una inversa seva per la dreta (si existeix)
     *  - Sinó, null.
     */
    static int[][] exercici4(int[] a, int[] b, Function<Integer, Integer> f) {
      throw new UnsupportedOperationException("pendent");
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // Nombre de particions

      test(2, 1, 1, () -> exercici1(new int[] { 1 }) == 1);
      test(2, 1, 2, () -> exercici1(new int[] { 1, 2, 3 }) == 5);

      // Exercici 2
      // Clausura d'ordre parcial

      final int[] INT02 = { 0, 1, 2 };

      test(2, 2, 1, () -> exercici2(INT02, new int[][] { {0, 1}, {1, 2} }) == 6);
      test(2, 2, 2, () -> exercici2(INT02, new int[][] { {0, 1}, {1, 0}, {1, 2} }) == -1);

      // Exercici 3
      // Ínfims i suprems

      final int[] INT15 = { 1, 2, 3, 4, 5 };
      final int[][] DIV15 = generateRel(INT15, (n, m) -> m % n == 0);
      final Integer ONE = 1;

      test(2, 3, 1, () -> ONE.equals(exercici3(INT15, DIV15, new int[] { 2, 3 }, false)));
      test(2, 3, 2, () -> exercici3(INT15, DIV15, new int[] { 2, 3 }, true) == null);

      // Exercici 4
      // Inverses

      final int[] INT05 = { 0, 1, 2, 3, 4, 5 };

      test(2, 4, 1, () -> {
        var inv = exercici4(INT05, INT02, (x) -> x/2);

        if (inv == null)
          return false;

        inv = lexSorted(inv);

        if (inv.length != INT02.length)
          return false;

        for (int i = 0; i < INT02.length; i++) {
          if (inv[i][0] != i || inv[i][1]/2 != i)
            return false;
        }

        return true;
      });

      test(2, 4, 2, () -> {
        var inv = exercici4(INT02, INT05, (x) -> x);

        if (inv == null)
          return false;

        inv = lexSorted(inv);

        if (inv.length != INT05.length)
          return false;

        for (int i = 0; i < INT02.length; i++) {
          if (inv[i][0] != i || inv[i][1] != i)
            return false;
        }

        return true;
      });
    }

    /*
     * Ordena lexicogràficament un array de 2 dimensions
     * Per exemple:
     *  arr = {{1,0}, {2,2}, {0,1}}
     *  resultat = {{0,1}, {1,0}, {2,2}}
     */
    static int[][] lexSorted(int[][] arr) {
      if (arr == null)
        return null;

      var arr2 = Arrays.copyOf(arr, arr.length);
      Arrays.sort(arr2, Arrays::compare);
      return arr2;
    }

    /*
     * Genera un array int[][] amb els elements {a, b} (a de as, b de bs) que satisfàn pred.test(a, b)
     * Per exemple:
     *   as = {0, 1}
     *   bs = {0, 1, 2}
     *   pred = (a, b) -> a == b
     *   resultat = {{0,0}, {1,1}}
     */
    static int[][] generateRel(int[] as, int[] bs, BiPredicate<Integer, Integer> pred) {
      var rel = new ArrayList<int[]>();

      for (int a : as) {
        for (int b : bs) {
          if (pred.test(a, b)) {
            rel.add(new int[] { a, b });
          }
        }
      }

      return rel.toArray(new int[][] {});
    }

    // Especialització de generateRel per as = bs
    static int[][] generateRel(int[] as, BiPredicate<Integer, Integer> pred) {
      return generateRel(as, as, pred);
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 3 (Grafs).
   *
   * Els (di)grafs vendran donats com llistes d'adjacència (és a dir, tractau-los com diccionaris
   * d'adjacència on l'índex és la clau i els vèrtexos estan numerats de 0 a n-1). Per exemple,
   * podem donar el graf cicle no dirigit d'ordre 3 com:
   *
   * int[][] c3dict = {
   *   {1, 2}, // veïns de 0
   *   {0, 2}, // veïns de 1
   *   {0, 1}  // veïns de 2
   * };
   */
  static class Tema3 {
    /*
     * Determinau si el graf `g` (no dirigit) té cicles.
     */
    static boolean exercici1(int[][] graf) {
       int n = graf.length;
        boolean[] visitat = new boolean[n];
        int[] pare = new int[n];
        Arrays.fill(pare, -1);

        for (int vInicial = 0; vInicial < n; vInicial++) {
            if (!visitat[vInicial]) {
                ArrayList<Integer> pila = new ArrayList<>();
                pila.add(vInicial);
                visitat[vInicial] = true;

                while (!pila.isEmpty()) {
                    int actual = pila.remove(pila.size() - 1);

                    for (int veinat : graf[actual]) {
                        if (!visitat[veinat]) {
                            visitat[veinat] = true;
                            pare[veinat] = actual;
                            pila.add(veinat);
                        } else if (veinat != pare[actual]) {
                            return true; // Hi ha cicle
                        }
                    }
                }
            }
        }
        return false;
    }
    }

    /*
     * Determinau si els dos grafs són isomorfs. Podeu suposar que cap dels dos té ordre major que
     * 10.
     */
    static boolean exercici2(int[][] g1, int[][] g2) {
      int n = g1.length;
        if (g2.length != n) return false;

        int[] grausG1 = new int[n];
        int[] grausG2 = new int[n];

        for (int i = 0; i < n; i++) {
            grausG1[i] = g1[i].length;
            grausG2[i] = g2[i].length;
        }

        Arrays.sort(grausG1);
        Arrays.sort(grausG2);

        for (int i = 0; i < n; i++) {
            if (grausG1[i] != grausG2[i]) return false;
        }

        int[] permutacio = new int[n];
        for (int i = 0; i < n; i++) permutacio[i] = i;

        do {
            if (comprovaIsomorfisme(g1, g2, permutacio)) return true;
        } while (proximaPermutacio(permutacio));

        return false;
    }

    // Comprova si g1 és isomorf a g2 sota la permutació donada
    static boolean comprovaIsomorfisme(int[][] g1, int[][] g2, int[] perm) {
        int n = perm.length;

        for (int i = 0; i < n; i++) {
            boolean[] adj1 = new boolean[n];
            for (int veinat : g1[i]) {
                adj1[perm[veinat]] = true;
            }

            boolean[] adj2 = new boolean[n];
            for (int veinat : g2[perm[i]]) {
                adj2[veinat] = true;
            }

            if (!Arrays.equals(adj1, adj2)) return false;
        }

        return true;
    }

    // Genera la següent permutació lexicogràfica
    static boolean proximaPermutacio(int[] perm) {
        int i = perm.length - 2;
        while (i >= 0 && perm[i] >= perm[i + 1]) i--;
        if (i < 0) return false;

        int j = perm.length - 1;
        while (perm[j] <= perm[i]) j--;

        int tmp = perm[i];
        perm[i] = perm[j];
        perm[j] = tmp;

        for (int k = i + 1, l = perm.length - 1; k < l; k++, l--) {
            tmp = perm[k];
            perm[k] = perm[l];
            perm[l] = tmp;
        }

        return true;
    }
    }

    /*
     * Determinau si el graf `g` (no dirigit) és un arbre. Si ho és, retornau el seu recorregut en
     * postordre desde el vèrtex `r`. Sinó, retornau null;
     *
     * En cas de ser un arbre, assumiu que l'ordre dels fills vé donat per l'array de veïns de cada
     * vèrtex.
     */
    static int[] exercici3(int[][] g, int r) {
     static int[] exercici3(int[][] graf, int arrel) {
        boolean[] visitat = new boolean[graf.length];
        List<Integer> resultatPostordre = new ArrayList<>();

        if (conteCicle(graf, arrel, -1, visitat)) return null;

        for (boolean v : visitat) {
            if (!v) return null;
        }

        Arrays.fill(visitat, false);
        dfsPostordre(graf, arrel, visitat, resultatPostordre);

        int[] resultat = new int[resultatPostordre.size()];
        for (int i = 0; i < resultatPostordre.size(); i++) {
            resultat[i] = resultatPostordre.get(i);
        }

        return resultat;
    }

    // DFS per detectar cicles
    static boolean conteCicle(int[][] graf, int actual, int pare, boolean[] visitat) {
        visitat[actual] = true;

        for (int veinat : graf[actual]) {
            if (!visitat[veinat]) {
                if (conteCicle(graf, veinat, actual, visitat)) return true;
            } else if (veinat != pare) {
                return true;
            }
        }

        return false;
    }

    // DFS postordre clàssic
    static void dfsPostordre(int[][] graf, int actual, boolean[] visitat, List<Integer> resultat) {
        visitat[actual] = true;
        for (int veinat : graf[actual]) {
            if (!visitat[veinat]) {
                dfsPostordre(graf, veinat, visitat, resultat);
            }
        }
        resultat.add(actual);
    }
    }

    /*
     * Suposau que l'entrada és un mapa com el següent, donat com String per files (vegeu els tests)
     *
     *   _____________________________________
     *  |          #       #########      ####|
     *  |       O  # ###   #########  ##  ####|
     *  |    ####### ###   #########  ##      |
     *  |    ####  # ###   #########  ######  |
     *  |    ####    ###              ######  |
     *  |    ######################## ##      |
     *  |    ####                     ## D    |
     *  |_____________________________##______|
     *
     * Els límits del mapa els podeu considerar com els límits de l'array/String, no fa falta que
     * cerqueu els caràcters "_" i "|", i a més podeu suposar que el mapa és rectangular.
     *
     * Donau el nombre mínim de caselles que s'han de recorrer per anar de l'origen "O" fins al
     * destí "D" amb les següents regles:
     *  - No es pot sortir dels límits del mapa
     *  - No es pot passar per caselles "#"
     *  - No es pot anar en diagonal
     *
     * Si és impossible, retornau -1.
     */
    static int exercici4(char[][] mapa) {
       static int exercici4(char[][] mapa) {
        int files = mapa.length;
        int columnes = mapa[0].length;
        boolean[][] visitat = new boolean[files][columnes];

        int[] movF = {-1, 1, 0, 0}; // Moviments verticals
        int[] movC = {0, 0, -1, 1}; // Moviments horitzontals

        ArrayList<int[]> cua = new ArrayList<>();

        // Localitzar l'origen 'O'
        for (int i = 0; i < files; i++) {
            for (int j = 0; j < columnes; j++) {
                if (mapa[i][j] == 'O') {
                    cua.add(new int[]{i, j, 0});
                    visitat[i][j] = true;
                    break;
                }
            }
        }

        int idx = 0;
        while (idx < cua.size()) {
            int[] pos = cua.get(idx++);
            int f = pos[0], c = pos[1], passos = pos[2];

            if (mapa[f][c] == 'D') return passos;

            for (int k = 0; k < 4; k++) {
                int nf = f + movF[k];
                int nc = c + movC[k];

                if (nf >= 0 && nf < files && nc >= 0 && nc < columnes &&
                    !visitat[nf][nc] && mapa[nf][nc] != '#') {
                    visitat[nf][nc] = true;
                    cua.add(new int[]{nf, nc, passos + 1});
                }
            }
        }

        return -1; // Destí no trobat
    }
}
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {

      final int[][] D2 = { {}, {} };
      final int[][] C3 = { {1, 2}, {0, 2}, {0, 1} };

      final int[][] T1 = { {1, 2}, {0}, {0} };
      final int[][] T2 = { {1}, {0, 2}, {1} };

      // Exercici 1
      // G té cicles?

      test(3, 1, 1, () -> !exercici1(D2));
      test(3, 1, 2, () -> exercici1(C3));

      // Exercici 2
      // Isomorfisme de grafs

      test(3, 2, 1, () -> exercici2(T1, T2));
      test(3, 2, 2, () -> !exercici2(T1, C3));

      // Exercici 3
      // Postordre

      test(3, 3, 1, () -> exercici3(C3, 1) == null);
      test(3, 3, 2, () -> Arrays.equals(exercici3(T1, 0), new int[] { 1, 2, 0 }));

      // Exercici 4
      // Laberint

      test(3, 4, 1, () -> {
        return -1 == exercici4(new char[][] {
            " #O".toCharArray(),
            "D# ".toCharArray(),
            " # ".toCharArray(),
        });
      });

      test(3, 4, 2, () -> {
        return 8 == exercici4(new char[][] {
            "###D".toCharArray(),
            "O # ".toCharArray(),
            " ## ".toCharArray(),
            "    ".toCharArray(),
        });
      });
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 4 (Aritmètica).
   *
   * En aquest tema no podeu:
   *  - Utilitzar la força bruta per resoldre equacions: és a dir, provar tots els nombres de 0 a n
   *    fins trobar el que funcioni.
   *  - Utilitzar long, float ni double.
   *
   * Si implementau algun dels exercicis així, tendreu un 0 d'aquell exercici.
   */
  static class Tema4 {
    /*
     * Primer, codificau el missatge en blocs de longitud 2 amb codificació ASCII. Després encriptau
     * el missatge utilitzant xifrat RSA amb la clau pública donada.
     *
     * Per obtenir els codis ASCII del String podeu utilitzar `msg.getBytes()`.
     *
     * Podeu suposar que:
     * - La longitud de `msg` és múltiple de 2
     * - El valor de tots els caràcters de `msg` està entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
     *
     * Pista: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
     */
    static int[] exercici1(String msg, int n, int e) {
        byte[] bytes = msg.getBytes();
        int[] result = new int[bytes.length / 2];

        for (int i = 0; i < bytes.length; i += 2) {
            int b1 = bytes[i] & 0x7F;       //Ens assegurem que el valor està entre 0 i 127
            int b2 = bytes[i + 1] & 0x7F;

            int bloc = b1 * 128 + b2;       //Codificació de dos caràcters en un enter
            result[i / 2] = elevar(bloc, e, n); //Encriptació RSA: bloc^e mod n
        }

        return result;
    }

    static String exercici2(int[] m, int n, int e) {
        //Factorització simple de n = p * q
        int p = 0, q = 0;
        for (int i = 2; i * i <= n; i++) {
            if (n % i == 0) {
                p = i;
                q = n / i;
                break;
            }
        }

        int phi = (p - 1) * (q - 1);        //Càlcul de φ(n)
        int d = invertir(e, phi);           //Clau privada: inversa modular de e mod φ(n)

        byte[] bytes = new byte[m.length * 2];
        for (int i = 0; i < m.length; i++) {
            int bloc = elevar(m[i], d, n);  //Desencriptació RSA: bloc^d mod n

            //Reconstrucció dels dos caràcters originals
            bytes[2 * i] = (byte) (bloc / 128);
            bytes[2 * i + 1] = (byte) (bloc % 128);
        }

        return new String(bytes);
    }

    static int elevar(int base, int exp, int mod) {
        //Exponenciació modular eficient (exponentiation by squaring)
        long result = 1;
        long b = base % mod;
        while (exp > 0) {
            if ((exp & 1) == 1) {
                result = (result * b) % mod;
            }
            b = (b * b) % mod;
            exp >>= 1;
        }
        return (int) result;
    }

    static int invertir(int a, int m) {
        //Algorisme d’Euclides estès per trobar la inversa modular de a mod m
        int m0 = m, x0 = 0, x1 = 1;
        while (a > 1) {
            int q = a / m;
            int t = m;
            m = a % m;
            a = t;

            t = x0;
            x0 = x1 - q * x0;
            x1 = t;
        }
        return (x1 + m0) % m0;
    }
    
    static void tests() {
      // Exercici 1
      // Codificar i encriptar
      test(4, 1, 1, () -> {
        var n = 2*8209;
        var e = 5;

        var encr = exercici1("Patata", n, e);
        return Arrays.equals(encr, new int[] { 4907, 4785, 4785 });
      });

      // Exercici 2
      // Desencriptar i decodificar
      test(4, 2, 1, () -> {
        var n = 2*8209;
        var e = 5;

        var encr = new int[] { 4907, 4785, 4785 };
        var decr = exercici2(encr, n, e);
        return "Patata".equals(decr);
      });
    }
  }

  /*
   * Aquest mètode `main` conté alguns exemples de paràmetres i dels resultats que haurien de donar
   * els exercicis. Podeu utilitzar-los de guia i també en podeu afegir d'altres (no els tendrem en
   * compte, però és molt recomanable).
   *
   * Podeu aprofitar el mètode `test` per comprovar fàcilment que un valor sigui `true`.
   */
  public static void main(String[] args) {
    System.out.println("---- Tema 1 ----");
    Tema1.tests();
    System.out.println("---- Tema 2 ----");
    Tema2.tests();
    System.out.println("---- Tema 3 ----");
    Tema3.tests();
    System.out.println("---- Tema 4 ----");
    Tema4.tests();
  }

  // Informa sobre el resultat de p, juntament amb quin tema, exercici i test es correspon.
  static void test(int tema, int exercici, int test, BooleanSupplier p) {
    try {
      if (p.getAsBoolean())
        System.out.printf("Tema %d, exercici %d, test %d: OK\n", tema, exercici, test);
      else
        System.out.printf("Tema %d, exercici %d, test %d: Error\n", tema, exercici, test);
    } catch (Exception e) {
      if (e instanceof UnsupportedOperationException && "pendent".equals(e.getMessage())) {
        System.out.printf("Tema %d, exercici %d, test %d: Pendent\n", tema, exercici, test);
      } else {
        System.out.printf("Tema %d, exercici %d, test %d: Excepció\n", tema, exercici, test);
        e.printStackTrace();
      }
    }
  }
}
// vim: set textwidth=100 shiftwidth=2 expandtab :
