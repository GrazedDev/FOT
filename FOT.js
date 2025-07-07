const mineflayer = require('mineflayer');
const axios = require('axios');
const fs = require('fs');
const nbt = require('prismarine-nbt');
const parseNbt = nbt.parse;
const atob = str => Buffer.from(str, 'base64');
const pLimit = require('p-limit');
const { LRUCache } = require('lru-cache');

// Core State
let skyblock = 0, island = 0, hasSpawned = false;
let currentPurse = 0, delayTime = 10000, lastApiUpdate = 0;
let state = 'init', stateTimestamp = Date.now();
let auctionsCache = [], auctionFetchPromise = null;

// Load config from JSON

const defaultConfig = {
    email: "",
    listUnder2ndLBin: 15, // % under 2nd lbin
    purchasing: true,
    maxPurchases: 3, // max purchases before listing items
    PROFIT_MARGIN_THRESHOLD: 0.5, // 50%
    MIN_RAW_PROFIT: 500000,
    maxPrice: 10000000000,
    stockMin: 40,
    excludeReforges: true,
    excludeStars: true,
    excludeSpecials: true,
    excludePetLevel: true,
    excludeRarities: false,
    excludeRaritiesForPets: false
};

const configFile = 'config.json';

if (!fs.existsSync(configFile)) {
    fs.writeFileSync(configFile, JSON.stringify(defaultConfig, null, 2));
    console.log("➣ Created default config.json");
}

const config = JSON.parse(fs.readFileSync(configFile));

//Config grabbing
const email = config.email;
const listUnder2ndLBin = config.listUnder2ndLBin;
const purchasing = config.purchasing;
const maxPurchases = config.maxPurchases;
const PROFIT_MARGIN_THRESHOLD = config.PROFIT_MARGIN_THRESHOLD;
const MIN_RAW_PROFIT = config.MIN_RAW_PROFIT;
const maxPrice = config.maxPrice;
const stockMin = config.stockMin;
const excludeReforges = config.excludeReforges;
const excludeStars = config.excludeStars;
const excludeSpecials = config.excludeSpecials;
const excludePetLevel = config.excludePetLevel;
const excludeRarities = config.excludeRarities;
const excludeRaritiesForPets = config.excludeRaritiesForPets;

// Constants
const Days = 24 * 60 * 60 * 1000;
const STARSTXT = ["✪", "✪✪", "✪✪✪", "✪✪✪✪", "✪✪✪✪✪", "✪✪✪✪✪➊", "✪✪✪✪✪➋", "✪✪✪✪✪➌", "✪✪✪✪✪➍", "✪✪✪✪✪➎"];
const SPECIALSTXT = ["✦", "⚚", "✿", "◆"];
const LVLTXT = [
    "[Lvl", "1]", "2]", "3]", "4]", "5]", "6]", "7]", "8]", "9]", "0]",
    "21]", "22]", "23]", "24]", "25]", "26]", "27]", "28]", "29]", "20]",
    "31]", "32]", "33]", "34]", "35]", "36]", "37]", "38]", "39]", "30]",
    "41]", "42]", "43]", "44]", "45]", "46]", "47]", "48]", "49]", "40]",
    "51]", "52]", "53]", "54]", "55]", "56]", "57]", "58]", "59]", "50]",
    "61]", "62]", "63]", "64]", "65]", "66]", "67]", "68]", "69]", "60]",
    "71]", "72]", "73]", "74]", "75]", "76]", "77]", "78]", "79]", "70]",
    "81]", "82]", "83]", "84]", "85]", "86]", "87]", "88]", "89]", "80]",
    "91]", "92]", "93]", "94]", "95]", "96]", "97]", "98]", "99]", "90]", "100"];
const REFORGES = [
    "Ancient", "Fabled", "Spiritual", "Suspicious", "Sharp", "Heroic", "Spicy", "Renowned", "Candied", "Submerged", "Gilded",
    "Dimensional", "Withered", "Burning", "Precise", "Shiny", "Snowy", "Thick", "Hot", "Strengthened", "Pitchin'", "Thicc",
    "Wise", "Clean", "Fierce", "Gentle", "Heavy", "Legendary", "Mythic", "Odd", "Pure", "Giant", "Glistening", "Light", "Very",
    "Loving", "Blessed", "Fleet", "Rooted", "Waxed", "Menacing", "Brilliant", "Bountiful", "Auspicious", "Scraped",
    "Smart", "Strong", "Superior", "Unpleasant", "Epic", "Fast", "Godly", "Hurtful", "Reinforced", "Necrotic", "Trashy",
    "Fair", "Royal", "Festive", "Blazing", "Fiery", "Jaded", "Rapid", "Titanic", "Rich", "Salty", "Treacherous", "Magnetic",
    "Lucky", "Deadly"];
const RARITIES = ["COMMON", "UNCOMMON", "RARE", "EPIC", "LEGENDARY", "MYTHIC", "DIVINE", "SPECIAL", "VERY SPECIAL", "SUPREME"];

// Caches
const HISTORY_FILE = 'priceHistory.json';
const PURCHASES_FILE = 'purchases.json';
const HISTORY_SORT_MODE = 'time';
const priceHistory = fs.existsSync(HISTORY_FILE) ? JSON.parse(fs.readFileSync(HISTORY_FILE)) : {};
const successfulPurchases = fs.existsSync(PURCHASES_FILE) ? JSON.parse(fs.readFileSync(PURCHASES_FILE)) : [];
const nameCache = new LRUCache({ max: 5000 });
const nbtCache = new LRUCache({ max: 2000 });

//Random
let lastClaimCheck = 0;
const CLAIM_INTERVAL = 5 * 60 * 1000; // 5 minutes
let purchaseList = [];
let title = "";
let currentPurchasedSlot = 0;
let currentPurchaseNumber = 0;
let pl1 = 0;
let pl2 = 0;
let slot = null;
let confirmed = null;

// Networking
const https = require('https');
const axiosInstance = axios.create({
    timeout: 5000,
    httpsAgent: new https.Agent({ keepAlive: true, maxSockets: 32 })
});
let isSpamChecking = false;
const attempts = 120;
const apiRefreshCycle = 60000;
const earlyPoll = 2000;
let skipNext = false;

function format(n) {
    return new Intl.NumberFormat().format(n);
}

function normalizeItemName(name, rarity) {
    if (!name) return "";
    let parts = name.split(" ");
    const isPet = parts.some(part => LVLTXT.some(lvl => part.includes(lvl)));

    if (excludePetLevel) parts = parts.filter(part => !LVLTXT.some(lvl => part.includes(lvl)));
    if (excludeReforges) parts = parts.filter(part => !REFORGES.includes(part));
    if (excludeStars) parts = parts.filter(part => !STARSTXT.includes(part));
    if (excludeSpecials) parts = parts.filter(part => !SPECIALSTXT.some(symbol => part.includes(symbol)));

    let normalized = parts.join(" ").replace(/\s+/g, ' ').trim();
    if (isPet) {
        if (!excludeRaritiesForPets) normalized = `${rarity} ${normalized}`;
    } else {
        if (!excludeRarities) normalized = `${rarity} ${normalized}`;
    }

    return normalized;
}

function getItemRarityFromLore(lore) {
    if (!lore) {
        return "UNKNOWN";
    }
    const loreText = lore.toUpperCase();
    for (const rarity of RARITIES.sort((a, b) => b.length - a.length)) {
        if (loreText.includes(rarity)) {
            return rarity;
        }
    }
    return "UNKNOWN";
}

function saveData() {
    fs.writeFileSync(HISTORY_FILE, JSON.stringify(priceHistory, null, 2));
    fs.writeFileSync(PURCHASES_FILE, JSON.stringify(successfulPurchases.sort((a, b) => new Date(b.timePurchased) - new Date(a.timePurchased)), null, 2));
    console.log("➣ Saved price history and purchase records to disk.");
}

function pruneOldHistory() {
    const now = Date.now();
    for (const key in priceHistory) {
        const before = priceHistory[key].length;
        priceHistory[key] = priceHistory[key].filter(e => now - e.time <= 7 * Days);
        const after = priceHistory[key].length;
        if (before !== after) console.log(`➣ Pruned ${before - after} old entries for "${key}"`);
    }
}

function sortPriceHistory() {
    for (const entries of Object.values(priceHistory)) {
        entries.sort((a, b) => b.time - a.time);
    }
}

async function fetchWithRetry(url, retries = 3, delay = 300) {
    for (let i = 0; i <= retries; i++) {
        try {
            return await axiosInstance.get(url);
        } catch (err) {
            console.warn(`➣ Fetch failed for ${url} (Attempt ${i + 1}): ${err.message}`);
            if (i === retries) {
                console.error(`➣ Exhausted retries for ${url}`);
                return null;
            }
            await new Promise(r => setTimeout(r, delay * (2 ** i)));
        }
    }
}

async function fetchAllAuctions() {
    console.log("➣ Starting to fetch all auctions from API...");
    const firstPage = await fetchWithRetry("https://api.hypixel.net/skyblock/auctions?page=0");
    if (!firstPage?.data?.success) {
        console.error("➣ Failed to fetch first auction page or API returned failure.");
        return [];
    }

    const totalPages = firstPage.data.totalPages;
    const lastUpdated = firstPage.data.lastUpdated;
    lastApiUpdate = lastUpdated;
    console.log(`➣ Total pages: ${totalPages}, lastUpdated timestamp: ${lastUpdated}`);

    const urls = Array.from({ length: totalPages }, (_, i) => `https://api.hypixel.net/skyblock/auctions?page=${i}`);
    const results = await Promise.all(urls.map(url => fetchWithRetry(url)));

    const auctions = results.flatMap(res => res?.data?.auctions?.filter(a => a.bin) || []);
    console.log(`➣ Total BIN auctions fetched: ${auctions.length}`);
    return auctions;
}

async function findProfitableFlips(auctions) {
    console.log("➣ Starting to analyze auctions for profitable flips...");
    const now = Date.now();
    const limit = pLimit(100);
    const grouped = Object.create(null);

    const parsedAuctions = await Promise.all(auctions.map(a => limit(async () => {
        if (!a.item_name || a.starting_bid < MIN_RAW_PROFIT / 2 || a.starting_bid > maxPrice) return null;

        let count = 1;
        try {
            const buf = atob(a.item_bytes);
            const parsed = await parseNbt(buf);
            count = parsed?.parsed?.value?.i?.value?.value?.[0]?.Count?.value || 1;
            nbtCache.set(a.item_bytes, count);
        } catch {
            count = 1;
            nbtCache.set(a.item_bytes, 1);
        }

        const rarity = getItemRarityFromLore(a.item_lore);
        const groupKey = normalizeItemName(a.item_name, rarity);
        const unitPrice = a.starting_bid / count;

        return { groupKey, unitPrice, count, uuid: a.uuid, fullPrice: a.starting_bid, name: a.item_name, time: now };
    })));

    for (const item of parsedAuctions) {
        if (!item) continue;
        const list = grouped[item.groupKey] ||= [];
        list.push(item);
    }

    const flips = [];
    for (const group in grouped) {
        const items = grouped[group];
        if (items.length < 2) continue;

        items.sort((a, b) => (a.unitPrice * a.count) - (b.unitPrice * b.count));

        const first = items[0];
        const second = items[1];
        const cost = first.unitPrice * first.count;
        const sell = second.unitPrice * second.count;
        const rawProfit = (sell - cost) * ((100 - listUnder2ndLBin) / 100);
        const margin = rawProfit / cost;

        if (margin > PROFIT_MARGIN_THRESHOLD && rawProfit > MIN_RAW_PROFIT && items.length >= stockMin) {
            flips.push({
                uuid: first.uuid,
                originalName: first.name,
                originalPrice: first.fullPrice,
                stackSize: first.count,
                pricePer: first.unitPrice,
                rawProfit,
                margin,
                stock: items.length
            });
        }
    }

    console.log(`➣ Flip analysis complete. Found ${flips.length} profitable flips.`);
    return flips;
}


function updatePurse(bot) {
    const sbitems = bot?.scoreboard?.sidebar?.items;
    if (!sbitems || sbitems.length === 0) {
        console.log("➣ No scoreboard items found.");
        return false;
    }

    const lines = sbitems.map((sbitem, index) => {
        try {
            const raw = sbitem.displayName.toString();
            const cleaned = raw
                .replace(/§[0-9a-fklmnor]/gi, '') // Strip Minecraft formatting codes
                .replace(/[^a-zA-Z0-9:., ]/g, '') // Keep only letters, numbers, colons, commas, and spaces
                .trim();
            return cleaned;
        } catch (e) {
            console.log(`➣ Error parsing scoreboard line [${index}]:`, e.message);
            return '';
        }
    });
    for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        if (line.includes("Purse")) {
            const combined = line + (lines[i + 1] || '');
            const match = combined.match(/Purse:?\s*([\d,]+)/i);
            if (match) {
                currentPurse = parseInt(match[1].replace(/,/g, ''), 10);
                console.log("➣ Current Purse updated: ", currentPurse);
                return true;
            } else {
                console.log("➣ Found 'Purse' but couldn't extract number from:", combined);
            }
        }
    }

    console.log("➣ Could not find or parse full purse value in scoreboard.");
    return false;
}

async function detectInitialDelayTime() {
    console.log("➣ Detecting initial delayTime...");

    try {
        let initialRes = await axios.get("https://api.hypixel.net/skyblock/auctions?page=0");
        let initialLastUpdated = initialRes.data.lastUpdated;

        console.log(`➣ Initial lastUpdated from API: ${initialLastUpdated}`);
        let newLastUpdated = initialLastUpdated;

        for (let i = 0; i < 180; i++) { 
            await new Promise(resolve => setTimeout(resolve, 500));

            const checkRes = await axios.get("https://api.hypixel.net/skyblock/auctions?page=0");
            newLastUpdated = checkRes.data.lastUpdated;

            if (newLastUpdated > initialLastUpdated) {
                delayTime = Date.now() - newLastUpdated;
                lastApiUpdate = newLastUpdated;
                console.log(`➣ Initial delayTime established: ${delayTime}ms`);
                return;
            } else {
            }
        }

        console.warn("➣ Timed out waiting for first api update.");
    } catch (err) {
        console.error("➣ Error during initial delayTime detection:", err.message);
    }
}


async function earlyApiSpamCheck() {
    if (isSpamChecking) {
        return;
    }

    isSpamChecking = true;
    console.log(`➣ Spamming lastUpdated check 5s before expected update...`);

    for (let i = 0; i < attempts; i++) {
        await new Promise(resolve => setTimeout(resolve));

        if (auctionFetchPromise) {
            console.log("➣ Fetch already in progress. Cancelling spam check.");
            break;
        }

        try {
            const res = await axios.get("https://api.hypixel.net/skyblock/auctions?page=0");
            const newUpdate = res.data.lastUpdated;

            if (newUpdate > lastApiUpdate) {
                delayTime = Date.now() - newUpdate;
                lastApiUpdate = newUpdate;

                console.log(`➣ Early API update detected! Adjusted delayTime to ${delayTime}ms`);
                console.log("➣ Triggering auction fetch...");

                auctionFetchPromise = fetchAllAuctions()
                    .then(data => {
                        auctionsCache = data;
                    })
                    .catch(err => {
                        console.error("➣ Fetch error:", err);
                    })
                    .finally(() => {
                        auctionFetchPromise = null;
                    });

                break;
            } else {
                console.log(`➣ Spam check [${i + 1}/${attempts}]: No update yet.`);
            }
        } catch (err) {
            console.warn(`➣ Spam-check [${i + 1}/${attempts}] failed: ${err.message}`);
        }
    }

    isSpamChecking = false;
}

async function itemHasSoldLore(item) {
    try {
        if (!item || !item.nbt || !item.nbt.value) return false;

        const nbtData = item.nbt;

        const display = nbtData.value.display;
        if (!display || !display.value || !display.value.Lore) return false;

        const lore = display.value.Lore.value.value;
        if (!Array.isArray(lore)) return false;

        return lore.some(line => line.includes('Sold!'));
    } catch (err) {
        console.log(`➣ NBT parse error: ${err}`);
        return false;
    }
}

async function claimSoldAuctions() {
    console.log("➣ Checking for sold auctions...");

    try {
        if (bot.currentWindow != null) {
            bot.currentWindow.requiresConfirmation = false;
            bot.closeWindow();
        }
        await new Promise(r => setTimeout(r, 500));
        bot.chat("/ah");
        await new Promise(r => setTimeout(r, 1000));

        bot.currentWindow.requiresConfirmation = false;
        await bot.clickWindow(15, 0, 0);
        await new Promise(r => setTimeout(r, 800));

        const window = bot.currentWindow;
        if (!window) {
            console.log("➣ Manage Auctions window did not open.");
            return;
        }

        let claimed = 0;
        for (let i = 0; i < window.slots.length; i++) {
            const item = window.slots[i];

            if (item && await itemHasSoldLore(item)) {
                await new Promise(resolve => setTimeout(resolve, 1000));
                if (bot.currentWindow != null) {
                    bot.currentWindow.requiresConfirmation = false;
                }
                await bot.clickWindow(i, 0, 0);
                await new Promise(resolve => setTimeout(resolve, 1000));
                if (bot.currentWindow != null) {
                    bot.currentWindow.requiresConfirmation = false;
                }
                await bot.clickWindow(31, 0, 0);
                claimed++;
                await new Promise(r => setTimeout(r, 500));
            }
        }

        if (claimed > 0) {
            console.log(`➣ Claimed ${claimed} sold item(s).`);
            updatePurse(bot);
        } else {
            console.log("➣ No sold items found in Manage Auctions.");
        }

        await new Promise(r => setTimeout(r, 500));
        bot.closeWindow(bot.currentWindow);
    } catch (err) {
        console.error("➣ Error during sold auction claim:", err.message);
    }
}

async function waitForWindow(titleSubstring, timeout = 5000) {
    return new Promise((resolve) => {
        let resolved = false;

        if (bot.currentWindow?.title?.includes(titleSubstring)) {
            return resolve(bot.currentWindow);
        }

        const handler = (window) => {
            if (window?.title?.includes(titleSubstring)) {
                resolved = true;
                bot.removeListener('windowOpen', handler);
                resolve(window);
            }
        };

        bot.on('windowOpen', handler);

        setTimeout(() => {
            if (!resolved) {
                bot.removeListener('windowOpen', handler);
                resolve(null);
            }
        }, timeout);
    });
}

function waitForPurchaseConfirmation(timeout = 5000) {
    return new Promise((resolve) => {
        function onMessage(message) {
            const msg = message.toString();
            if (msg.includes("Visit the")) {
                bot.removeListener('message', onMessage);
                resolve(true);
            }
        }
        bot.on('message', onMessage);

        setTimeout(() => {
            bot.removeListener('message', onMessage);
            resolve(false);
        }, timeout);
    });
}

const bot = mineflayer.createBot({
    host: 'mc.hypixel.net',
    username: email,
    auth: 'microsoft',
    version: '1.8.9'
});

global.bot = bot;

bot.on('spawn', async () => {
    if (hasSpawned) return;
    hasSpawned = true;

    await detectInitialDelayTime();

    console.log("➣ Entering main loop...");
    loop();
});
async function loop() {
    const now = Date.now();

    if (state === 'init' && now - stateTimestamp >= 6000) {
        bot.chat('/play skyblock');
        console.log("➣ Sent /play skyblock command.");
        state = 'joinedSkyblock';
        stateTimestamp = now;
    } else if (state === 'joinedSkyblock' && now - stateTimestamp >= 6000) {
        bot.chat('/is');
        console.log("➣ Sent /is command to join island.");
        state = 'wentIsland';
        stateTimestamp = now;
    } else if (state === 'wentIsland' && now - stateTimestamp >= 6000 && updatePurse(bot)) {
        console.log("➣ Island joined and purse updated.");
        await claimSoldAuctions();
        state = 'mainLoop';
        stateTimestamp = now;
    } else if (state === 'mainLoop') {
        const projected = lastApiUpdate + delayTime + apiRefreshCycle;
        const wait = projected - Date.now();

        if (!auctionFetchPromise && wait <= earlyPoll && !isSpamChecking) {
            console.log("➣ Triggering API spam check...");
            earlyApiSpamCheck();
        }

        if (auctionsCache.length > 0) {
            const auctions = auctionsCache;
            auctionsCache = [];

            const flips = await findProfitableFlips(auctions);
            console.log(`➣ Found ${flips.length} flips.`);
            if (bot.currentWindow) {
                bot.closeWindow(bot.currentWindow);
            }

            for (const flip of flips) {
                if (bot.currentWindow) {
                    bot.closeWindow(bot.currentWindow);
                }
                if (!purchasing || currentPurse < flip.originalPrice || purchaseList.length >= maxPurchases) continue;
                console.log(`➣ Attempting purchase for ${flip.originalName} at ${format(flip.originalPrice)} coins with a profit of ${flip.rawProfit}`);
                await bot.chat(`/viewauction ${flip.uuid}`);

                let purchaseSuccessful = false;

                for (pl1 = 0; pl1 < 4400; pl1++) {
                    if (bot.currentWindow) {


                        await new Promise(r => setTimeout(r, 5));
                        const window = bot.currentWindow;
                        const title = window?.title?.toString() || "";

                        if (title.includes("BIN")) {
                            if (bot.currentWindow.slots) {
                                const slot = window.slots[31];

                                if (slot?.name === "gold_nugget" || slot?.name === "bed") {
                                    bot.currentWindow.requiresConfirmation = false;
                                    await bot.clickWindow(31, 0, 0);
                                } else {
                                    console.log(`➣ Unexpected item in auction slot: ${slot?.name || 'None'}`);
                                    if (slot) {
                                        pl1 = 99999999;
                                        bot.closeWindow(bot.currentWindow);
                                    }
                                }
                            }
                        }
                        else { await new Promise(r => setTimeout(r, 5)); }
                    }
                    else { await new Promise(r => setTimeout(r, 5)); }
                    if (bot.currentWindow) {
                        const confirmWindow = bot.currentWindow;
                        const confirmTitle = confirmWindow?.title?.toString() || "";
                        if (confirmTitle.includes("Confirm")) {
                            for (let pl2 = 0; pl2 < 160; pl2++) {
                                await new Promise(r => setTimeout(r, 5));
                                const confirmWindow = bot.currentWindow;

                                if (!confirmWindow || !confirmWindow.slots) {
                                    console.log("➣ Confirm window is missing or closed unexpectedly.");
                                    await new Promise(r => setTimeout(r, 5));
                                }
                                else {

                                    const confirmSlot = confirmWindow.slots[11];
                                    let confirmed = false;

                                    if (confirmSlot?.name === "stained_hardened_clay") {
                                        bot.currentWindow.requiresConfirmation = false;
                                        await bot.clickWindow(11, 0, 0);

                                        try {
                                            confirmed = await waitForPurchaseConfirmation(22000);
                                        } catch (err) {
                                            console.error("➣ Purchase confirmation failed:", err.message);
                                            confirmed = false;
                                            if (bot.currentWindow) {
                                                bot.closeWindow(bot.currentWindow);
                                            }
                                        }

                                        const purchaseRecord = {
                                            timePurchased: new Date().toISOString(),
                                            valuePurchased: flip.originalPrice,
                                            projectedSaleValue: flip.rawProfit + flip.originalPrice,
                                            itemName: flip.originalName
                                        };

                                        if (confirmed) {
                                            console.log("➣ Purchase confirmed by chat message.");
                                            purchaseList.push(purchaseRecord);
                                            purchaseList.sort((a, b) => new Date(a.timePurchased) - new Date(b.timePurchased));
                                            successfulPurchases.push(purchaseRecord);
                                            pl1 = 99999;
                                            pl2 = 99999;
                                        } else {
                                            console.log("➣ Purchase confirmation chat message not received in time.");
                                            pl1 = 99999;
                                            pl2 = 99999;
                                        }
                                    } else {
                                        console.log(`➣ Unexpected confirm item: ${confirmSlot?.name || 'None'}`);
                                    }
                                }
                            }
                        }

                    }
                }

            }
            if (now - lastClaimCheck > CLAIM_INTERVAL) {
                await claimSoldAuctions();
                lastClaimCheck = now;
            }

            if (purchaseList.length > 0) {
                console.log("➣ Purchased items:", purchaseList);

                for (let i = 0; i < purchaseList.length; i++) {
                    console.log("➣ Claiming item from AH...");
                    await new Promise(r => setTimeout(r, 600));
                    bot.chat("/ah");

                    const ahWindow = await waitForWindow("Auction House");
                    if (!ahWindow) continue;

                    ahWindow.requiresConfirmation = false;
                    await bot.clickWindow(13, 0, 0);
                    await new Promise(r => setTimeout(r, 600));
                    let bidsWindow = await waitForWindow("Your Bids", 3000);

                    await new Promise(r => setTimeout(r, 400));

                    for (let retry = 0; retry < 3 && !bidsWindow; retry++) {
                        bidsWindow = await waitForWindow("Your Bids", 2000);
                        if (!bidsWindow) {
                            console.log(`➣ Retry ${retry + 1}: Waiting for 'Your Bids' window...`);
                            await new Promise(r => setTimeout(r, 300));
                        }
                    }
                    if (!bidsWindow) continue;

                    bidsWindow.requiresConfirmation = false;
                    await bot.clickWindow(10, 0, 0);
                    await new Promise(r => setTimeout(r, 400));

                    const viewWindow = await waitForWindow("BIN Auction View");
                    if (!viewWindow) continue;

                    viewWindow.requiresConfirmation = false;
                    await bot.clickWindow(31, 0, 0);
                    console.log("➣ Claimed item.");
                    await new Promise(r => setTimeout(r, 500));
                }
            }

            if (purchaseList.length > 0) {
                console.log("➣ Purchased items:", purchaseList);

                for (let i = 0; i < purchaseList.length; i++) {
                    const listing = purchaseList[i];
                    const slotMap = [81, 82, 83, 84, 85, 86, 87, 88, 54, 55, 56, 57, 58, 59, 60, 61];
                    const currentPurchasedSlot = slotMap[i] || 81;
                    console.log(`➣ Starting listing for item #${i + 1}: ${listing.itemName}`);

                    let success = false;
                    for (let attempt = 0; attempt < 3 && !success; attempt++) {
                        console.log(`➣ Listing attempt ${attempt + 1} for ${listing.itemName}`);

                        if (bot.currentWindow) {
                            console.log("➣ Closing existing window...");
                            bot.closeWindow(bot.currentWindow);
                        }

                        bot.chat("/ah");
                        console.log("➣ Sent /ah command");
                        await new Promise(r => setTimeout(r, 1000));

                        const ahWindow = await waitForWindow("Auction House", 3000);
                        if (!ahWindow) {
                            console.log("➣ Failed to open Auction House window.");
                            continue;
                        }

                        bot.currentWindow.requiresConfirmation = false;
                        await bot.clickWindow(15, 0, 0);

                        console.log("➣ Waiting for 'Manage Auctions' window...");
                        await new Promise(r => setTimeout(r, 800));

                        const manageWindow = await waitForWindow("Manage Auctions", 3000);
                        if (!manageWindow) {
                            console.log("➣ 'Manage Auctions' window not found. Checking if we're already in 'Create BIN Auction' window...");
                            const listingWindow = await waitForWindow("Create BIN Auction", 3000);
                            if (!listingWindow) {
                                console.log("➣ Neither 'Manage Auctions' nor 'Create BIN Auction' window found. Retrying...");
                                continue;
                            }
                            skipNext = true;
                        }

                        if (skipNext === false) {
                            console.log("➣ Clicking 'Create Auction' button...");
                            bot.currentWindow.requiresConfirmation = false;
                            console.log("➣ Searching for golden_horse_armor to click 'Manage Auctions'...");

                            const manageSlot = bot.currentWindow?.slots.find((item, idx) => item && item.name === 'golden_horse_armor');
                            if (manageSlot) {
                                const slotIndex = bot.currentWindow.slots.indexOf(manageSlot);
                                console.log(`➣ Found 'Manage Auctions' at slot ${slotIndex}`);
                                await bot.clickWindow(slotIndex, 0, 0);
                            } else {
                                console.log("➣ Could not find 'Manage Auctions' (golden_horse_armor) in the window.");
                                return;
                            }
                            await new Promise(r => setTimeout(r, 800));

                            console.log("➣ Waiting for 'Create BIN Auction' window...");
                            const listingWindow = await waitForWindow("Create BIN Auction", 3000);
                            if (!listingWindow) {
                                console.log("➣ 'Create BIN Auction' window did not open.");
                                continue;
                            }
                        }

                        skipNext = false;

                        //console.log(`➣ Selecting purchased item from inventory slot ${currentPurchasedSlot}...`);
                        bot.currentWindow.requiresConfirmation = false;
                        await bot.clickWindow(currentPurchasedSlot, 0, 0);
                        await new Promise(r => setTimeout(r, 800));

                        //console.log("➣ Clicking BIN icon (slot 31)...");
                        bot.currentWindow.requiresConfirmation = false;
                        await bot.clickWindow(31, 0, 0);

                        //console.log("➣ Waiting to enter BIN price into sign...");
                        bot._client.once('open_sign_entity', ({ location }) => {
                            const value = Math.floor(listing.projectedSaleValue);
                            //console.log(`➣ Entering BIN value: ${value}`);
                            bot._client.write('update_sign', {
                                location: { x: location.x, y: location.y, z: location.z },
                                text1: `"${value}"`,
                                text2: '{"italic":false,"extra":["^^^^^^^^^^^^^^^"],"text":""}',
                                text3: '{"italic":false,"extra":["Your auction"],"text":""}',
                                text4: '{"italic":false,"extra":["starting bid"],"text":""}'
                            });
                        });

                        await new Promise(r => setTimeout(r, 800));
                        //console.log("➣ Clicking 'Confirm BIN' (slot 29)...");
                        bot.currentWindow.requiresConfirmation = false;
                        await bot.clickWindow(29, 0, 0);

                        await new Promise(r => setTimeout(r, 800));
                        //console.log("➣ Clicking 'Create Auction' (slot 11)...");
                        bot.currentWindow.requiresConfirmation = false;
                        await bot.clickWindow(11, 0, 0);

                        await new Promise(r => setTimeout(r, 800));
                        //console.log("➣ Closing current window...");
                        bot.currentWindow.requiresConfirmation = false;
                        await bot.closeWindow(bot.currentWindow);

                        console.log(`➣ Successfully listed item #${i + 1}: ${listing.itemName}`);
                        success = true;
                    }

                    if (!success) {
                        console.log(`➣ Failed to list item after 3 attempts: ${listing.itemName}`);
                    }
                }

                purchaseList = [];
                console.log("➣ Finished listing all items!");
            } else {
                console.log("➣ No purchases recorded yet.");
            }
            updatePurse(bot);
            pruneOldHistory();
            sortPriceHistory();
            saveData();
        }
    }

    setImmediate(loop);
}





