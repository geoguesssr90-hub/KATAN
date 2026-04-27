// Import the functions you need from the SDKs you need
import { initializeApp } from "firebase/app";
import { getAnalytics } from "firebase/analytics";
// TODO: Add SDKs for Firebase products that you want to use
// https://firebase.google.com/docs/web/setup#available-libraries

// Your web app's Firebase configuration
// For Firebase JS SDK v7.20.0 and later, measurementId is optional
const firebaseConfig = {
  apiKey: "AIzaSyCC2qmWJW2Fk-IPSZ_R5BTRD7_KWPqK0Qo",
  authDomain: "katan-app.firebaseapp.com",
  projectId: "katan-app",
  storageBucket: "katan-app.firebasestorage.app",
  messagingSenderId: "1063868983418",
  appId: "1:1063868983418:web:465a1cf3052d1aad85f3c3",
  measurementId: "G-V3P6SX8D5H"
};

// Initialize Firebase
const app = initializeApp(firebaseConfig);
const analytics = getAnalytics(app);