# A könnyűzene formális modellje

## Abstract
A zenei jelfeldolgozással foglalkozó algoritmusok gyakran figyelmen kívül hagyják magának a zenének az elméletét. Ennek oka a formális zenei modell hiánya. A munkámban megmutatom, hogy a formalizált zeneelmélet felhasználható a jelfeldolgozási kimenetek gépi elbírálásában. Megvizsgálom, hogy a zenei modell megválasztása hogyan befolyásolja a feldolgozás egyes szintjeit, hogyan lehet segítségükre, és hogyan verifikálhatóak számítógéppel az eredményeik. Arra is kitérek, hogy ez a számítási zenetudományi feladat milyen szoftvertechnológiai kihívásokkal jár, és azok hogyan oldhatóak meg.  

## A kutatási célok meghatározása

A kutatás legfőbb célja megállapítani, hogy milyen eszközökkel lehetséges a zene modelljét formalizálni oly módon, hogy a kész modell könnyen beágyazható legyen zenei jelfeldolgozási feladatokba. Ennek hasznossága illetve szükségessége több szinten megnyilvánul valós projektekben.

[zenei modell szintjei kép: 1. követelmények, dokumentációk 2. reprezentálás 3. zeneelméleti definíciók, függvények 4. zenei kiértékelés]()

A zenei modell hiánya legalacsonyabb szinten a feladat megfoglamazásánál, a követelmények egyértelmű definiálásánál jelentkezik. A zenei projektekre jellemző, hogy mivel leggyakrabban zenei háttértudással rendelkező fejlesztők készítik azokat, a zenészek által ismert zeneelmélet mentén fogalmaznak, ezek  viszont gyakran pontatlanok tudnak lenni a különböző zenei stílusok különböző fogalmazásai miatt. John Rahn is ebből indul ki a *Logic, Set Theory, Music Theory* című kutatásában, melyben így fogalmaz: "The music-theoretical literature is a porridge of definitions fallen prey to various dangers, and worse, of "definitions" so-called which are utterances of every possible sort except the sort of definition. If only authors who cannot define would confine themselves to the "you know what I mean" mode of discourse, all would be well. But a statement falsely purporting to define, if taken seriously, utterly destroys the fabric of its context.". Fontos hozzátenni, hogy a művészet központú zeneelmélet nem tekinti céljának a formalizáltságot, ezért alátámasztható, hogy miért hoz meg döntéseket több esetben akár hagyomány alapján is. Ha a zeneelmélet ezen alapvető hiányosságától el is tekintünk, akkor is nehezen található olyan zeneelméleti összefoglaló, ami a hanghullámoktól a zenei formáig és stílusokig egybefüggően tárgyalja a témát, így tehát általánosságban rossz gyakorlat a művészeti zeneelmélet használata követelmények megfogalmazásánál.

[Kép béna zenei dokumentációról]()
[Példa ellentmondó zeneelmélet könyvekből (konszonancia)]()

A modell szerepe a zenei adatok tárolásában is megjelenik. Dalok reprezentálására két módszert használnak a gyakorlatban. Az egyik a hangok MIDI fájlként való tárolása. Ennek egyértelmű hátránya, hogy a ritmikai információ kinyerése feldolgozást igényel. Ennek oka, hogy a hangok kezdete és vége van csak eltárolva, a hangérték megállíptása pedig sok esetben nem egyértelmű ezek alapján. Minden hanghoz a hang magasságán kívűl még a hang erősségének értéke van feljegyezve. Ennek a számnak az interpretálása szintén nem egyértelmű, hiszen egyszerre fejezi ki a hangszer hangerejét, a hang dinamikáját, a dal adott részének a dinamikáját illetve akár a hang ütemben kapott szerepét is. Ezen indokok miatt a MIDI formátum bár a zene fizikai leírásának megfelelő reprezentáció tud lenni, sok esetben további feldolgozást igényel, így általánosságban véve nem tekinthető magasszintű zenei jelfeldolgozási feladatoknál megfelelő kimeneti formátumnak.

[MIDI példa, esetleg valami nem egyértelmű ritmikai dologról]()

A zeneművek másik reprezentálási formája jellemzően valamilyen kottaszerű ábrázolást jelent. Bár ezen a területen megvalósítás és célkitűzések szempontjából széles skálán mozognak az eszközök, gyakori probléma viszont a jelfeldolgozáshoz való használatukban, hogy nem magát a zenét, hanem a kottát reprezentálják, ez pedig azon felül, hogy szükségtelen komplikációkat okoz, több esetben félrevezeti a fejlesztőket az eredmények értékelésénél, vagy a célok meghatározásában. Erre példaként hozható az ütemmutató és az ütemen belüli hangsúlyozás feljegyzése. Mivel az ütemmutató meghatározza, hogy az adott ütemen belül mely hangokra kerül nagyobb hangsúly, ezeken a hangokon kottában a megfelelő hangsúlyozást külön jelölni felesleges, viszont jelfeldolgozási feladatoknál minden egyes hang pontos hangsúlyozását elhagyni nagymértékű adatkiesést jelentene és nagyban megnehezítené a további feldolgozást. Ezen kívűl a kottába feljegyezhető dinamikai kifejezések gépi értelmezése lehetetlen vállalkozás lenne, ezek nélkül viszont nem megfelelő a zene reprezentálása kottában, így a kotta bár megfelelő végkimeneti formátum magasszintű jelfeldolgozási feladatoknak, a feladat végrehajtása közben viszont rossz gyakorlat a használata. Fontos megjegyezni, hogy léteznek olyan kottaszerű reprezentáló eszközök, amelyek jól kezelnek a most említett nehézségek közül többet is.

[Kotta példa]()
[Music21 nem is olyan rossz példa]()
[reprezentálás szintjei: alul MIDI felül kotta középen hiányzik a megfelelő eszköz]()

Egy általános zenei modellre a jelfeldolgozás során mint függvény gyűjteményre is szükség van. Erre a problémára számos zeneelmélet könyvtár létezik, viszont ezek saját típusokat használnak, amik nehezen kapcsolódnak zenei reprezentációs eszközökhöz. Másik általános hiányosságuk, hogy a fizikai zeneelmélet definícióit nem tartalmazzák.

[Music21 voicing dolog hogy viszonyul egy többszólamú rész reprezentálásához MIDI-ben?]()

Legmagasabb szinten pedig a zene formális modellje használható lenne jelfeldolgozó algoritmusok kimenetének zenei kiértékelésére. Bár ez használat szempontjából nem különül el a korábban említett zeneelmélet könyvtár eszközöktől, abból a szempontból fontos elkülöníteni mégis, hogy ez a feladat sokkal magasabb szintű zenei formalizálást igényel. Példaként hozható egy dal részeinek megnevezése, vagy műfajának felismerése.

[Ide is valami]()

A modell formalizálásnak eszközének megválasztásán kívül megvizsgálom, azt is, hogy melyek azok a zeneelméleti területek illetve konkrét feladatok amelyeket egy ilyen modellnek tárgyalnia kell annak érdekében, hogy mai jelfeldolgozási feladatokat megfelelően tudjon támogatni. Az elmúlt évtizedekben a számítási zenetudomány leginkább klasszikus zene köré épített elemzéseket, melyek sokszor könnyűzenére nem értelmezhetőek, illetve az könnyűzenére átültethető analízisek közül is kevés olyan akad, aminek gyakorlati haszna lenne egy tipikus mai projektben. Az elmúlt években robbanásszerűen növekedett a zenei jelfeldolgozás alkalmazása. Megjelent a streaming szolgáltatóknál és a zenei megosztó felületeken is, megbízható működésüknek szükségét pedig mi sem fejezné ki jobban, mint hogy eredményeik gyakran jogi következményeket vonnak maguk után. A futurisztikusnak tűnő okoserősítőkben pedig nem ritka funkció már a virtuális zenekar, amely minden instrukció nélkül real time kíséri a játékost a dalban, vagy akár együtt improvizál vele. Egy ilyen eszköz korábban nem látott feladatok merülnek fel. 

Vizsgálni fogom a zenei analízis alapvető kérdését, a zene és nem zene elválasztását. Minél szigorúbb állításokkal fogom szűkíteni a könnyűzene fogalmát és tanulmányozni fogom ennek a szigorításnak a jelentősségét. Kitérek az ütem és az ehhez tartozó fogalmak jelentésére, különböző definiálási lehetőségeire és az ezekhez tartozó ütemmutató felismerésének lehetséges megvalósításaira. Végül pedig megvizsgálom, hogy milyen fogalmak mentén definiálható a zenei variáció és a variáció mentén hogyan adható meg egy dal felépítése és részeinek kapcsolata.

 - Szakdogám akkordelnevezője is azért olyan szuper, mert sokat tud a program a zenéről
 - zeneelmélet formális alapjait lerakni



## A problémakör irodalmának, az előzményének rövid áttekintése

A számítási zenetudomány területén írt kutatásokról elmondható, hogy leggyarkabban egy újfajta zenei analízist mutatnak be, vagy egy már megírt részleteit taglalják. Az elmúlt közel hatvan évben számos olyan analízis illetve ezekhez tartozó feladat akadt, melynek nagy jelentőséget nyilvánított a szakma. Ebben a fejezetben ezek közűl a legelterjedtebb négyet fogom bemutatni röviden és vizsgálni a relevanciáját a könnyűzene formális modelljének jelfeldolgozási feladatokban betöltött szerepének szempontjából, illetve körüljárom, hogy megvalósításuk hogyan lenne lehetséges.

### Schenkeri zeneelmélet, generatív grammatika és halmazelmélet

Heinrich Schenker zeneelmélete számos zenei analízis alapjává vált, mivel ez volt az első olyan formálisnak ható rendszer, amellyel meghatározható egy zene felépítése a formától egészen a dallam szintjéig. Lényege abban rejlik, hogy szabályok mentén az eredeti zenét abstract zenei felépítéssé egyszerűsíti, így adva magyarázatot egy adott zenei résznek. Ezek az absztrakt zenei felépítések, hiszen továbbra is zenéről beszélünk, tovább egyszerűsíthetőek. A legmagasabb szintű absztrakt kivonat, az úgynevezett alapvető struktúra (Ursatz) nagyjából megegyezik minden egyes tonális műnél, így ez az elmélet alkalmas arra, hogy megmutassa egy adott zenemű egyedisége milyen szinten lép fel, illetve jól rávilágít két mű közötti különbség szintjére is.

[Schenkeri példa]()

Mivel Schenker zeneelmélete átírási szabályokon alapul, nagyon jól kapcsolatba hozható Chomsky transformációs generatív grammatikájával. Ezen az ötleten alapul Stephen W. Smoliar *A Computational Aid for Schenkerian Analysis* című cikkje, melyben az említett zenei analízist elvégző program működését részletezi. Ennek megvalósítása során Smoliar felismerte, hogy a Schenkeri zeneelmélet alapvető problémája az aluldefiniáltásg, így az csak alapgondolatok ötleteként szolgált a saját zeneelméletének formalizálásában.

[Példa a generatív grammatika és a schenkeri analízis hasonlatára]()
[Példa a Smoliar cikkből]()

Smoliar mellett John Rahn is kutatásában próbát tesz egy formális, de a Schenkeri zeneelmélethez hasonló modell felépítésére. A *Logic, Set Theory, Music Theory* című cikkében egy kezdetleges modellt épít fel halmazelmélettel, viszont a sorravett definíciókban hamar megjelennek korábban nem definiált zenei kifejezések, melyeket később sem tárgyal.

[IVA IVC mi az, hogy oktáv? hogy lehet IVC nélkül definiálni?]()
[Nem tudom, belerakjam-e, de a whole tone skála nem cyclic ordering]()

A kutatás arra is kitér, hogy a modell több szintaktikailag helyes, de elkerülendő, "ronda" zenei értelmezést is tud generálni. Ugyanígy "ronda" zeneművek is generálhatóak a modellből, vagy máshogy fogalmazva "nem zenék" is értelmezhetőek vele. Rahn szerint hiábavaló próbálkozás olyan elmélet megalkotásán dolgozni, amivel csak szép zenék és a legszebb elemzések állíthatóak elő.


### A tonális zene generatív elmélete (GTTM)

Fred Lerdhal és Ray Jackendoff 1977-es *Toward a Formal Theory of Tonal Music* kutatása új gondolatokat hozott a zene formalizálásának területére. Kitűzték, hogy a zeneelméletnek legalább négy doménje van, névlegesen csoportosító analízis, metrikus analízis, időintervallum redukció, és prolongációs redukció. Ezt a négyest a tonális zene generatív elméletének nevezték el. A modelljükben mind a négy elemzéshez a lehetséges struktúrális leírások meghatározására **well-formedness** szabályokat, a lehetséges leírások közötti a "tapasztalt hallgatónak" megfelelő leírás kiválasztására pedig **preference** szabályokat definiáltak. A csoportosító analízis a zenebén szereplő hangcsoportok hierarchiai rendjét adja meg, a metrikus analízis pedig az erős és gyenge ütések rendjét. A prolongációs redukció erősen párhuzamba hozható a Schenkeri zeneelmélettel, céljában megegyezik vele, míg a szabályokat a formalizáltság érdekében ahogy Smoliarnál és Rahnnál is láthattuk, máshogy kényszerűl definiálni. Az időintervallum redukció abban tér el a prolongációs redukciótól, hogy az egyszerűsítést a zene hangcsoportjain értelmezi.

[példa legalább egy analízisre szabályokkal]()

### Összegzés a könnyűzene és a jelfeldolgozás szemszögéből 

Az említett cikkek jól szemléltetik a tudományág kutatásainak fókuszát. Bármely cikk, amely egy elméletet tárgyal, a tonális klasszikus zenét teszi az analízis mindenkori bemenetévé, bár egyértelmű, hogy sokkal nagyobb számban van szükség könnyűzene elemzésére. Ezt tekintve fontos a kérdés tehát, értelmezhetőek-e a klasszikuszene analítikai módszerei könnyűzenén? Mielőtt ezt a kérdést tovább bontanám, fontos megemlíteni a zenetudósok között egy nagyon elterjedt nézetet, az elemzési partikularizmust. **ide kell hivatkozás** A partikularista zenetudósok nem nyilvánítanak nagy jelentőséget az univerzális zenei elemzéseknek, mert úgy gondolják hogy a zeneművek egyediségéből következik, hogy analítikai eszközeiket is egyedileg kell megválasztani. A korábbi kérdés helyett tehát jobb feltenni azt, hogy milyen a könnyűzenére általánosan megállapítható tulajdonság kinyerésére lehet szükség a jelfeldolgozási feladatok során. A korábban bemutatott analíziseknél megfigyelhető, hogy nem fektetnek hangsúlyt az analízis céljának meghatározására, vagyis arra, hogy milyen információ kinyerésének a feladatát valósítja meg, hanem elsősorban lépéseit vázolják. Éppen ezért csak a saját analízisünk célkitűzései után lehet megvizsgálni, hogy a korábbi zeneelméletek közül felhasználható-e valamelyik a feladatra, ezt pedig egy formális rendszerben igazolni is tudnánk. *Értelmezhetőek-e akkor a klasszikuszene analítikai módszerei a könnyűzenén?* Sajnos a válasz az, hogy nem tudjuk, egyáltalán célravezető-e értelmezni őket, bár valószínűleg értelmezhetőek, azonban azt sem tudhatjuk biztosan, hogy az eredmény mit fog jelenteni.

Ugyanennyire fontos, de egyszerűbb kérdés a következő: hogyan használhatóak fel ezek az analízisek zenei jeleken? Természetesen nem egy hatalmas lépésben szeretnénk kinyerni az információt a hanghullámból. A tipikus részfeladatok közé tartozik a különböző transzformációkkal a zenei adat, vagyis a zenei hangok kinyerése. A feladat ezen szintjén amikor zenei hangról beszélünk, igazán egy frekvenciára, egy kezdeti és befejezési időpontra, és különböző dinamikai jellemzőkre gondolunk. Ezeket a primitív zenei hangokat megfelelően tudjuk például MIDI-ben ábrázolni. Ahogy láthattuk az említett cikkek, ber erre külön nem térnek ki, de kottán definiálják az elemzéseket. Ez a gyakorlat elfogadható, lévén céljuk kész zeneművek leirat alapján történő elemzése. Ahhoz azonban, hogy ezeket felhasználhassuk jelfeldolgozás során is, a primitív zenei hangokat valahogyan kottába kell szednünk, vagy definiálnunk alacsonyabb szintre az eredeti analízisekkel megegyező analíziseket. Akárhogy is, a kotta és a nem kotta között tátongó lyukat, névlegesen az ütemmutatót, ritmust, hangnemet és hangneveket valahogyan át kell hidalni.

[hanghullám != primitív hang != kotta]()

A számítási zenetudomány irodalmát összevetve könnyűzenei jelfeldolgozás feladatával elmondható, hogy bár vannak jelentős átfedések, a hiányosságok ennél nagyobbak. A hiány először is az adatok reprezentálásának szintjén jelenik meg. A MIR egyik legfontosabb teendőjének tekinti a zenei adatok megfelelő reprezentálást a következő lépés végrehajtásának érdekében, amíg az említett irodalom megelégszik a kottával. Ezenkívűl a formalizáltság hiányát mutatja az, hogy a zenei analízisek szinte minden esetben implementáció nélkül, gyakran szavakkal megfogalmazott szabályokkal jelennek meg, így nehézzé téve alkalmazásukat valós projektekben. Az irodalom végső hiányossága pedig funkcióbeli. Sok a jelfeldolgozás során felmerülő zeneelméleti problémát nem tárgyal, például a hangok ütembeszedését, mivel ahogy korábban láthattuk ez az alacsonyabb zenei szint nem létezik az irodalomban. Ez a különbség kényszeríti ki azt a zeneelméletet, ami már nem a musicγ, hanem a musicυ elemzésére, tehát a zene, mint leirat helyett a zene, mint hang objektum elemzésére szolgál.

[music görögbetűk táblázata, hivatkozás]()

## A téma feldolgozás során alkalmazott módszerek

A munkám legfontosabb célja megállapítani, hogy a zene modellje a lefektetett kritériumoknak megfelelően milyen eszköz használatával formalizálható. A legjelentősebb technológiai kritérium a valós jelfeldolgozási projektekbe való könnyű integrálhatóság. A már létező zenét leíró modellekre jellemző, hogy projekt orientáltak, tehát könnyen bevonhatóak valós feladatokba, viszont ezt leginkább a a formális pontosság feláldozásával érik el, így ebben a fejezetben ebből a két szemszögből nézve határozom meg a megfelelő eszközt a feladatra, példákat mutatva kész modellekből.

### Az eszköz megválasztásáról

A (számítási) zenei formalizáltságot sokféle képpen el lehet érni. A megvalósítás eszközei három csoportba sorolhatóak. Az első csoportnak nevezhetjük a fájlkonvenciókat. Ezeknek alapvető felhasználási területüknek jellemzően a felhasználói programok adattárolását tekinthetjük. Gondolhatunk akár kottaszerkesztő alkalmazásokra, akár zenei perifériák stúdió programokkal való kommunikáicójára, egyes esetekben akár primitív zenelejátszási felhasználásra is, például retró stílusú játékoknál. Ebbe a kategóriába tartozik a kottaszedés formalizálásaként is felfogható MusicXML és Lilypond, illetve a zenei előadás formalizálásaként felfogható MIDI formátum is. Ezeket a már kész modelleket projektbe való bevonás szempontjából vizsgálva megállapítható egyértelműen, hogy alkalmasak rá. Így a kérdés már csak az, hogy megfelelnek-e a mi formális zene követelményeinknek, vagyis tárgyalják-e azokat a területeket, ahol a zenei modell hiánya fellép (lásd ábra).

[Zenei modell hiánya megint]()

A fájlkonvenciók ha implicit módon is, de definiálnak zenei kifejezéseket, ilyen definíció például MusicXML-ben az ütemmutató, vagy MIDI-ben a hang fogalma. 

[MusicXML, MIDI implicit definíció kikövetkeztetése]()

A fájlkonvencióra épülő zenei modellek hiányossága azonban az egyoldalúságukban rejlik. Bár a kotta és a zenei előadás is a zenét írja le, de mégis érezhető, hogy ezek formalizálása nem valósítja meg a zene teljes formalizálását. A valóság az, hogy a zene egy igazán öszetett képzelt tárgy, melynek **.....** kutatása szerint négy doménje létezik, a zene, mint **felsorolni...**. Így már egyértelmű, hogy a MusicXML és a Lilypond esetében a music**?** formalizálásról, míg MIDI esetében a music**?** formalizálásról van szó. Egy optimális modell azonban mind a négy domént tárgyalná és lehetőleg definiálná a közöttük lévő kapcsolatot is. Ez a hiányosság teszi alkalmatlanná ezeknek a zenei modelleknek a jelfeldolgozási feladatokban kizárólagos modellként való használatát. A fájlkonvenciókra továbbá kategorikusan is elmondható, hogy nem fognak tudni zeneelméleti függvénygyűjtemény, illetve a zenei kiértékelés hiányán segíteni lévén nem futtathatóak.

A második kategória a zenei modell megvalósításának eszközeiben a program csomagok. Ezekre jellemző, hogy jelfeldolgozás érdekében készítették őket, így az eddig taglalt követelményeink mindegyikének valahogy megfelelnek. Ilyen eszköz az MIT kutatói által fejlesztett Music21, vagy éppen a Mingus nevű python package. A zene négy doménjére visszatekintve felvetődik a kérdés, vajon tárgyalják-e ezek az eszközök mindegyiket. Általánosan megfigyelhető, hogy valamilyen kevert modellt állítanak fel, ami bár nagyon szoros kapcsolatban áll a kottával, vagyis a tiszta zenei leirattal, de emellé beemelnek tulajdonságokat a zene jobban fizikai oldaláról is. Ez a gyakorlat felfogható a zenei leirat egy alacsonyabb, a kottához viszonyítva hiperrealisztikus szintjének.

[Music21 kottaszerűen modellezi a zenét, de kitér a fizikai dolgokra is (mennyire hamis a hang, milyen dinamikai ereje van]()

Bár a Music21, mint legjobb zeneelméleti programcsomag is több szinten hiányos, például a zene alacsony (fizikai) és magas (formai) szintjén, illetve az irodalomhoz hűen a tonális klasszikus zenét teszi egyenlővé a zenével, de bővíthetőségének köszönhetően ezek pótolhatóak lennének, így kategorikusan a programcsomag, mint technológiai megvalósítása a zenei modellnek nem utasítható el ezek alapján. Így a kérdés jelen technológiánál már csak az, hogy mennyire tekinthetó jó formális definíciónak egy Python függvény. Tekintsük az alábbi példát:

[Valami egyszerű függvény music21ből és ugyanaz papíron formalizálva]()

Az első különbség a papíron és a Pythonban írt definíció között, hogy míg az előbbi a természetes számokon definiálja a **....**-ot, a forráskód az **Int?** standard libraryben szereplő típuson. Bár a neve jelzi, hogy valami hasonló dologról van itt szó, köztudott, hogy ezek különbözően vannak definiálva és működésükben is eltérnek. Vegyük például az alábbi esetet:

[Valami állítás a függvényről, ami papíron működik, de pythonban nem]()

Vajon ez az általános működésbeli eltérés van-e akkora jelentőségű, hogy az egyszerű programcsomagok helyett másik eszköz keresés felé forduljunk? A zenei jelfeldolgozás talán nem a legbiztonságkritikusabb terület, így a matematikai megfelelés ilyen szintű hiányosságát el lehet fogadni a zenei modell implementációjában, azonban az eszköz használata során ezzel a korlátozással tisztában kell lennünk. Az előző példa azonban nem csak ezt szemlélteti. Azt is megmutatja, hogy előfordul, hogy állításokat akarunk felírni a definíciókra. A munkámnak nem célja részletezni, hogy imperatív nyelvek milyen lehetőségeket kínálnak erre a célra, mivel az belátható, hogy a matematikai megegyezés hiányában az állítások ha felírhatók is, szigorúbbak lennének a szükségesnél, belátások pedig bonyolultabb. Programcsomagok azonban léteznek funkcionális nyelvekhez is, melyeknél a tárgyalt reprezentációs probléma elkerülhettő, így egyszerűen felírhatóak állítások.

[Funkcionális nyelven felírt állítás]()

A harmadik kategória a zenei modell megvalósításának eszközei között funkcionális nyelvek vonálon továbbhaladva a proof assistant programcsomagok kategóriája. Ezek az eszközök a funkciónális nyelveken felírható bizonyítások megoldására való "bizonyítási nyelvvel" való kibővítését jelentik. Ezek közül a két legelterjedtebb eszköz az Agda illetve a Coq. Jelenleg egyik nyelvhez sem létezik komoly zeneelméleti könyvtár, azonban megállapítható, hogy formalizálás szempontjából minden korábbi követelményünk megvalósítására megfelelőek lennének. Egy proof assistantben megírt zenei modellben a zene minden szintjén megfelelően felírhatóak lennének a definíciók, az imperatív nyelvekre jellemző megszorítások nélkül, továbbá egyszerűen megfogalmazhatóak lennének a hipotézisek, melyek bizonyításához ráadásul elegendő a papíron megszokotthoz hasonlóan a bizonyítás vázlatát, nem pedig a bizonyító függvényt megadni.

[Bizonyítás Coqban vázlattal, és a legenerált függvény]()

Belátva, hogy zenei formalizálás szempontjából a proof assistant programcsomag megfelel minden kritériumunknak, térjünk vissza az eszköz megválasztásának projektekbe való integrálásának szempontjához. Eddig nem volt szükséges pontosan definiálni ennek kikötéseit, de összegezve alapvetően három szempontból kell jól szerepelnie egy eszköznek, hogy használható legyen valós projektekben. Először is bevonható kell, hogy legyen azokba a nyelvekbe, amelyeken a zenei jelfeldolgozás projektjei tipikusan íródnak. Másodszor lehetőleg minél gyorsabbnak kell lennie (a konkrét zenei feladatok elvégzésében), hiszen zenei jelfeldolgozási projektek nem ritka követelménye a valósidejűség. Harmadikként pedig preferálandó egy olyan eszköz, melynek használata nem áll túl messze a területen dolgozó tipikus fejlesztőktől, mivel ahogy a legtöbb programcsomagnál, itt is a minőség egyik mutatója a projekt életbenmaradása és dinamikus fejlődése, ami egyetemi kutatócsoportot vagy opensource projektet tekintve a fejlesztők cserélődése miatt a minél kevésbé meredek betanulási görbével érhető csak el.

Mielőtt az Agda és a Coq, mint a két legelterjedtebb proof assistant különbségeit a felsorolt szempontok szerint áttekintenénk, fontos megemlíteni a hasonlóságaikat is. Mindkét nyelvben a matematikai bizonyítások és a programkód közötti kapcsolatot a Curry-Howard izomorfizmus valósítja meg, mely röviden annyit jelent, hogy egy függvény felfogható bizonyításként is. Az alábbi példa ezt szemlélteti. Mindkét nyelv Martin Löf függő típusos elméletén alapul melynek célja a konstruktív matematikai felépítést támogatni.

[Curry-Howard wikipédia példa]()

A két eszköz közötti legnagyobb használatbeli különbség, hogy míg Coqban a bizonyítás vázlatának írására definiálva van egy külön nyelv, az úgy nevezett "taktikák nyelve", addig Agdában erre nincs külön eszköz. Bár általánosságban elmondható, hogy a szintaxis kifejezetten nem számít, a korábban felsorolt harmadik technológiai kritérium miatt mégis érdemes megemlíteni, hogy míg az Agda Haskell szerű szintaxist nyújt, addig a Coq egy elsőre szokatlanabb formátummal bír. Mindkét nyelven valamilyen szinten interaktív a fejlesztés folyamata. A Coqhoz tartozó CoqIDE soronként interpretálja a programkódot, míg Agdában egy sokkal magasabb szintű, parancsokon alapuló interakciós felület használható, melyet Emacs bővítményként szolgáltatnak. A projektebe való integrálhatóság szempontjából legjelentősebb különbség azonban a kód extraktálása más nyelvbe. Coqban lehetőség van OCaml vagy Haskell kód exportálására, míg az Agda nem támogatja ezt a funkciót. Végül ez az utolsó különbség az, ami miatt valószínüleg jobb döntés a Coqot választani a zenei modell formalizálásához jelfeldolgozási feladatoknál. A feladatomat tehát egy Coq libraryvel fogom megoldani. **Ezt biztosan ki lehetne jobban fejteni**

### Definíciók

A modell leírására Coq definíciókat, állításokat és bizonyításokat használok fel. A tesztelést oly módon valósítom meg, hogy a definíciókról tulajdonságokat fogalmazok meg állításként, melyeket adott értékekre bebizonyítok. Ez a gyakorlat párhuzamba hozható a unit teszteléssel. Több esetben az állításokat általánosan is megfogalmazom. Az ilyen általános tulajdonságok belátása a unittesztelésnél egy sokkal erősebb eszköz. Ezekkel azonban elsődleges célom nem a megfelelő működés bebiztosítása (hiszen nem is létezik egy sablonként használható modell), hanem egy szép elmélet felépítése, melynek mozgatórugója a matematikáéhoz hasonló összefüggések sokasága. Szemelőtt tartom tehát John Rahn gondolatát, miszerint "a formalizálásnak épp úgy vonzó az esztétikus döntés, mint a praktikus".

 - Benson Mates' Elementary Logic (197-203): A definíció eliminable és non-creative kell, hogy legyen


## A téma feldolgozásának részletezése, részletes ismertetése

**a felépítést még át kell gondolni**
A munkám céljai között korábban kitűztem, hogy az eszköznek négy szinten kell támogatnia a zenei jelfeldolgozást. Ebben a fejezetben kitérek rá, hogy egyes szinteken ez hogyan valósul meg, illetve ezt egyszerű példákon szemléltetem is. A fejezet egyszerre zenei modell reprezentációs szintjein keresztül vezet végig a zenei modell hiányának szintjein.

[modell szintjei megint]()

A következőkben taglalt Coq library neve Bremen lett.

[brémai muzsikusok]()

### A zenei hang formalizálásáról

Korábban már említettem, hogy a számítási zenetudomány irodalma jellemzően nem részletezi a zenei hang reprezentálását, hanem ehelyett a kottára támaszkodva épít fel elméleteket. Elvétve azonban mégis lehet találni pár elgondolást a hang tulajdonságairól. Azokat a zenei kifejezéseket, amelyek használata nem egységes az irodalomban az egyértelműség kedvéért a továbbiakban angolul használom.

| angol        | magyar                | angol műszótár szerint[hiv]()    | magyar műszótár szerint[hiv]() |
|-------------|----------------------|-------------------|---|
| pitch        | hangmagasság          | A hang magassága vagy mélysége            | A hangnak az a sajátossága, ami a hangot előidéző rezgések számától függ |
| note         | hangjegy              | A zene lejegyzésére használt szimbólumok  | A hangok magasságának és viszonylagos időtartamának jelölésére és megrögzítésére szolgáló különleges írásjelek |
| register     | regiszter             | Különböző részei egy hangszer vagy énekhang hangterjedelmének  | |
| pitch class  |                      |                   |

Az alábbi két példa John Rahn modelljének első definíciója, illetve S. W. Smoliar megjegyzése saját modelljéről.

```
x is a note IFF x = <z, <T1, T2>> for some value of z, T1, T2.

Ahol z egy hangmagasság, T1 a hang kezdeti, T2 pedig a befejezési időpontja, úgy, hogy a nulla időpont a megfontolás alatt álló mű kezdetét jelöli egy tetszőleges vagy képzeletbeli előadás során.
```

```
A note két elemből álló listaként van reprezentálva, ezek a pitch és a register. [...] A pitch továbbá lehet diatonikus vagy kromatikus. A diatonikus pitcheket a C, D, E, F, G, A, B szimbólumok reprezentálják. A kromatikus pitchet egy két elemű lista reprezentálja, melynek első eleme egy módosítójel, második eleme pedig egy pitch.
```

A példákból láthatjuk, hogy a definíciók nem egyeznek meg egymással, sőt a szavak általánosan elfogadott jelentésétől is eltérnek. John Rahn esetében a problémát az jelenti, hogy a note időbeliségét nem a ritmika mentén, tehát egymáshoz viszonyított hosszuk alapján, hanem egy művön belüli abszolút elhelyezés szerint határozza meg. Hiányossága pedig, hogy a pitch definiálására nem tér ki, ez azonban Smoliar munkájából kiderül, hogy nem is teljesen egyértelmű feladat. Smoliar modelljében zenei kifejezések átnevezeését, vagy méginkább félrenevezését tapasztalhatjuk. Láthatóan a tudományos pitch lejegyzéshez (SPN) hasonlóan szeretne definiálni dolgokat, leegyszerűsítve betűk, módosítójelek és számok segítségével (például C##3), azonban a helyes pitch kifejezés helyett noteként hivatkozik erre. A leírását kijavítani teljesen úgy lehet, hogy az eredetileg pitchként elnevezett fogalmat pitch classre kereszteljük, mely éppen azt jelenti, amit a megadott definíció is. A pitch class ílymódon való megadásának a számítást a továbbiakban jelentősen bonyolító hibája, hogy felírhatóak `[# , [b , [# , A]]]` formájú felesleges kifejezések is. Smoliar modellje tehát nem tartalmaz a note jelentésének megfelelő formalizációt, így az időbeliséget ebben az elméletben csak a rákövetkezés fejezi ki.

Ezek alapján a helyes formalizáció a Bremenben a pitch szintjéig a következő:

```coq
(* harmony.Letter.v *)
Inductive letter : Type := | A | B | C | D | E | F | G.

(* harmony.PitchClass.v *)
Inductive pitchClass : Type :=
  pitch_class : letter -> Z -> pitchClass.

Notation "L # M" := (pitch_class L M) (at level 80, right associativity).

(* harmony.Pitch.v *)
Inductive pitch : Set :=
  p : pitchClass -> nat -> pitch.

Notation "PC ' O" := (p PC O) (at level 85, right associativity).

Example C1  := (C # 0)   ' 1.
Example Gbb4 := (G # - 2) ' 4.
```

Ez a reprezentálás egyértelműen (és helyesen) különíti el a szinteket és megfeleltethető az SPN-nek azzal a különbséggel, hogy a módosítójelek, mivel azok szintaktikai cukorként is felfoghatóak, nem képezik részét a reprezentációnak, hanem helyettük a módosítás mértékét egy egész szám jelöli, ahol a pozitív a keresztek és a negatív a bék irányát mutatja, így elkerülve a szabálytalan pitchek lejegyzését.

Az eddigi formalizálás megfelel a zenei szótáraknak, azonban ez a párhuzam a note szintjén elkezd szétválni. Ennek oka, hogy a note a kottához kötött dolog, azonban egy optimális zenei modell a zene minden csatornáját magában foglalná, melyek közül a zenei lejegyzés, a kotta csak az egyik. A musicυ (zene, mint hangobjektum) formalizáláshoz való közelítés egyik lehetséges formája minél több fizikai tulajdonsággal ellátni a note-ot. Vegyük az alábbi típust:

```coq
(* harmony.Note.v *)
Inductive note : Type :=
  | note_of : pitch -> duration -> dynamic -> note
  | rest_of : duration -> dynamic -> note.
```

Hogy a szünet a note részét képezi nem szép ezen a szinten, viszont a későbbi definíciók így esztétikusabban alakulnak. Ezt a gyakorlatot láthatjuk John Rahnnál és a Music21-ben is. A duration a zenei hosszúságot reprezentáló típus, melyre később kitérek. A dynamic a note dinamikai tulajdonságát írja le. Ez több féle képpen is definiálható, attól függően, hogy milyen részletességel szeretnénk a zenéről beszélni. Például jelfeldolgozási feladatoknál tudjuk pontosan azokat a fizikai attribútumokat használni, amelyeket az adott transzformációkkal meg tudunk állapítani, de tetszés szerint le tudjuk szűkíteni kottára jellemző kifejezésekre is. Ezt szemlélteti a két leegyszerűsített példa.

```coq
(* represents starting, middle and ending velocity *)
Inductive dynamic : Type :=
  dyn : nat -> nat -> nat -> dynamic.
```

```coq
Inductive dynamic : Type :=
| f
| mf
| mp
| p .
```

Note és a pitch különválasztásának köszönhetően definiálhatjuk zenei hangok időtől elvont struktúrját is. Ezzel a felépítéssel akkordokat és skálákat is reprezentálhatunk, így általános elnevezésnek a Chord szót választottam. Ezekről a zenei felépítésekről a zeneelmélet gyakran még általánosabban, az időn kívűl a hang magasságának regiszterbeli tulajdonságától is eltekintve beszél és hoz állításokat. Az ilyen típusú definíciók is könnyen megadhatóak a pitch és a pitch class különválasztásának köszönhetően a Chordhoz hasonlóan felépíthető AbstractChord típussal.

```coq
chord
abstractchord
```

A bemutatott típusokra számos állítás definiálható, melyeket alapvetően elvárnánk, hogy egy zenei modellben teljesüljenek. Ahogy láthattuk, előfordul azonban, hogy olyan dolog reprezentálására kényszerülünk, melyről nem olvastunk még korábban, így hasonlítási alapunk sincsen, így összesen a praktikusság és az esztétika az amire támaszkodhatunk.

```coq
bizonyítás
```

A zenei jelfeldolgozási feladatok megvalósításának első nehézsége, ami a modell hiányából adódik, az a formális követelmények elmaradása, illetve a fejlesztői dokumentáció pontatlan megírása. Ezeknél a feladatoknál akár egy zeneelméleti programcsomag definícióihoz, akár egy zenei műszótárhoz igazodunk, nagyon könnyen találhatunk hibásan, vagy aluldefiniált részeket, amelyek legrosszabb esetben csak a program megvalósítása utána a tesztelésnél jelentkeznek. Ilyen helyzetekben a fejlesztő mindenképpen rosszul jár, hiszen azt kell eldöntenie, hogy elfogadja-e a modell nem megfelelő formalizálását, amin a már kész jelfeldolgozás alapszik, vagy nem. Tekintsük az alábbi példát. **.....**

[példa, mingus hangközeit felhasználva?]()

Ebben az esetben a Bremen választásához mérlegelni kell, hogy az említett problémák kiküszöbölésének érdekében megéri-e az új technológia megismerésébe fektetett energia. Egyetemi kutatócsoportokat szemelőtt tartva elmondható, hogy igen. Muszáj utoljára még egyszer feltenni a kérdést, vajon megoldjuk-e egy ilyen eszköz használatával általánosságban az összen ilyen jellegű problémát? Azt feltehetjük, hogy a rendszer formálisan megfelelően definiált, állításokkal és (Coq által elfogadott) bizonyításokkal teleírt, így az imperatív programcsomagokhoz képest mindenképpen megfelelőbb eredményre számíthatunk ezen a téren. Tudjuk tehát, hogy egy formális zenei modellről van szó, de az viszont megfontolandó dolog, hogy ez a modell megfelel-e zenei szempontból, tehát azt fejezei-e ki, amit elvárnánk tőle. Ezen döntés mellett a területen tapasztalható zenei modell konszenzusának hiányában az egyetlen érv éppen csak a korábban olvasható törekvések listája tud lenni. Ha elfogadjuk tehát, hogy a Bremen egy "jó" zeneelmélet, az alapján, hogy éppen erre törekszik, akkor viszont már rendet tudunk rakni az összes többi zenei definíció és modell között.

```coq
mingus rossz definíció
```

**képezés a frekvenciákba,
követelményeknél nem lehet egy az egybe a coqot használni, de coqban le lehet írni állításokatt a zenei kifejezésekre, ezekre lehet hivatkozni a követelményekben.
**

### A ritmus formalizálásáról

A ritmus a zenei műszótár szerint a hangok időrendi sorrendjének rendje, egymáshoz való időértékviszonya. Ennek megfelelően vegyük az alábbi formalizációt:

```coq
(* rhythm.Division.v *)

Inductive division : Type :=
    | whole
    | half : division -> division
    | third : division -> division
  .
```

```coq
(* rhythm.Duration.v *)

Inductive duration : Type :=
  | dur : division -> duration
  | tie : duration -> duration -> duration.
```

A hangok hosszának egymáshoz való viszonyításának eszköze a duration, vagyis a hossz típusa, mely a division, vagyis a leosztás segítégével épül fel. A ritmus tehát a hosszok listáját jelenti. A leosztás elméletileg bármilyen prímszámmal megtörténhet, például öttel a pentola esetén, ettől azonban eltekintek az eszköz jelen állapotában, mivel ezek a könnyűzenében aligha fordulnak elő.

[negyedhang képen és coqban, stb.]()
[egy dallam, beirogatva a durationökkel és divisionökkel]()

Bár egy dallam nem más, mint hangjegyek listája, a számítási zenetudomány területén megalkotott dallam analízisek között bőven léteznek olyanok, amelyek pusztán hangjegyek listáján, az ütemekbe tördeltség hiánya miatt még sem értelmezhetőek. Az ütemvonal a kottában egy elválasztó eszköz, mely amellett, hogy segít a kottán belüli tájékozódásban, a zene hangsúlyozását fejezei ki, az ütemekhez tartozó ütemmutató pedig az ütem hosszát illetve az ütem alapvető felosztási egységét adja meg. Mivel a zenei jelfeldolgozás során kezdetben a zenei információt MIDI szerüen, tehát időben elhelyezett hangmagasságokként tudjuk kinyerni, ahhoz, hogy például a Schenkeri zeneelméleten alapuló valamelyik formális elemzést alkalmazni tudjuk, muszáj ütemekbe tördelni a hangokat. Ez a feladat tekinthető jelfeldolgozási számítási zenetudomány legfontosabb problémájának.

Az ütem és a zene kapcsolatát elemezve számos megfigyelést tehetünk. Először is, a zene formai részei, mint például versszak és refrén, leggyakrabban egy ütem végéig tartanak és egy ütem elején kezdődnek.

[kotta]()

Az akkordváltások szintén leggyakrabban ütem elején, vagy közepén történnek.

[kotta]()

Gyakran ritmikailag szimmetrikusan épülnek fel az ütemek.

[kotta]()

Nem utolsó sorban pedig gyakran ritmikailag és dallamilag is párhuzam vonható két ütem között.

[kotta]()

Ezek mentén tehát elképzelhető egy hangjegyek listáján értelmezett ütembe tördelő analízis, amely sok esetben megfelelően működne, főleg ha figyelembe vesszük, hogy ezek a tulajdonságok minden egyes hangszer szólamában külön külön előfordulnak és ezek nem mindig esnek egybe, viszont az ütemeknek egybe kell esniük a teljes dalon minden hangszeren. Ez egyértelműen nem tudna minden esetben jól működni, de nem kizárt, hogy elég jól működne ahhoz, hogy eredményesen segítse a további zenei analízist, ezért az ütembetördelés ezenfajta megvalósítása további kutatást igényel. Az azonban belátható, hogy egy ilyen megvalósításnak a Coq nem is lenne a legjobb technológiai választás, ráadásul állításokat sem tudnánk megfogalmazni a feladat és a megvalósítás között. Egy másik megoldás utáni keresés utolsó indokaként pedig tekintsük a GTTM csoportosító analízisének szabályait. Látható, hogy a prefrencia szabályok ugyanazokat a szempontokat részesítik előnyben, amelyeket mi is előnyben részesítenénk az ütemvonalak behúzására, azonban a csoportosító analízis célja nem az ütemek meghatározása, hanem az értelmileg összefüggő egységek határainak megkeresése, ami a példából látszik, hogy előfordul, hogy nem esik egybe.

[dia hetedik sor 5, 6 szabály]()
[dia 6. oldal kotta]()

Felmerül a kérdés, hogy mit is jelent akkor igazán az ütem? A műszótár úgy fogalmazza meg, hogy az ütem az a metrikus egység, ami mindig két főhangsúly (úgynevezett egy) közé esik. A főhangsúlyt egyéb definíció hiányában a legnagyobb hangsúlyok kategóriájának tekintve az ütemvonal jelentése nem más, mint a rákövetkező hangjegy erős hangsúlyozása. Ennek mentén könnyen definiálható egy dallamra az ütemekké tördelő analízis, hiszen egyszerűen szét kell választeni minden olyan hangjegy előtt, amely rendelkezik az "egy érzettel", vagyis főhangsúlyos.

```coq
Inductive dynamic : Type :=
| oneFeel
(* ... *) 
.
```

Érezhető, hogy ezzel a lépéssel inkább csak egy lejjebbi szintre toltuk a problémát, mintsem megoldottuk. A kérdés most már hogy hogyan ismerhető fel a főhangsúly? A zenei hangsúlyozás négy eszköze közül leggyakoribb dinamikai kiemelés, ami nem más, mint a hang nagyobb hangerővel való megszólaltatása. A hangsúly második formája a harmóniai kiemelés, vagyis egy erőteljes akkord is képes jelölni a főhangsúlyt. A hangsúly ezen formájától egyelőre tekintsünk el a harmóniai erőteljesség nehézkes definiálása miatt. A hangsúlyt ki lehet fejezni a hang enyhe meghosszabbításával, vagy késleltetett kezdésével is. Ezeket általánosan ritmikai hangsúlynak nevezzük, azonban ezek a hangjegyek felfogott ritmikáját nem befolyásolják így a ritmikai változtatás lejegyzésre sem kerülhet. A hangsúlyozás negyedik eszköze a könnyűzenében soha elő nem forduló dallami hangsúlyozás, melynek alkalmazásakor a hangsúlyos hangnak enyhén megváltozik a magassága.

**az ütemmutató nem része a zenének, de megállapítható róla
példa: egy ütemmutató algoritmus kiértékel egy hangfájlt, én pedig a modellemmel a hangfájl leiratának birtokában megmondom, hogy jó-e. Végülis egy bizonyítás, de igazán csak egy unit teszt.**

### A többszólamúság formalizálásáról
 - dallam
 - többszólamú zene lehetséges formalizálásai
 - variáció definiálása
 - a zene részeinek elkülönítése

### A hangobjektum formalizálásáról

### A modell beágyazása projektekbe
 - példa paraméterezhető automatikus bizonyításra, amit egy másik program használni tud
 - a modellt lehet végülis szintetizálásra használni, így könnyen előállíthatók algoritmusoknak teszt esetek, amiket könnyű vizsgálni

## Az eredmények összefoglaló értékelése és a levonható következtetések

 - mit lehetett bebizonyítani a zenei struktúrákra
 - mindent kapcsolatba hoz az eszköz mindennel: Midit a kottával, művészi zeneelméletet a fizikával, zenetudományi kutatásokat jelfeldolgozási projektekkel
 - Toward a formal theory 2. oldal "One of the virtues of formal theory ..."
