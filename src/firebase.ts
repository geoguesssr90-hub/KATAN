import { initializeApp } from "firebase/app";
import { getDatabase, ref, set, get, onValue, off } from "firebase/database";


const firebaseConfig = {
  apiKey: "AIzaSyCC2qmWJW2Fk-IPSZ_R5BTRD7_KWPqK0Qo",
  authDomain: "katan-app.firebaseapp.com",
  projectId: "katan-app",
  storageBucket: "katan-app.firebasestorage.app",
  messagingSenderId: "1063868983418",
  appId: "1:1063868983418:web:465a1cf3052d1aad85f3c3",
  measurementId: "G-V3P6SX8D5H",
  databaseURL: "https://katan-app-default-rtdb.asia-southeast1.firebasedatabase.app",
};

const app = initializeApp(firebaseConfig);
export const db = getDatabase(app);
export { ref, set, get, onValue, off };